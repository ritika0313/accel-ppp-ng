#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <fcntl.h>
#include <string.h>
#include <ctype.h>
#include <errno.h>
#include <stdint.h>
#include <limits.h>
#include <sys/socket.h>
#include <sys/ioctl.h>
#include <openssl/hmac.h>
#include <openssl/evp.h>
#include "linux_ppp.h"

#include "log.h"
#include "events.h"
#include "ppp.h"
#include "ppp_ccp.h"
#include "ppp_ipv6cp.h"
#include "ipdb.h"

#include "memdebug.h"

#define INTF_ID_FIXED  0
#define INTF_ID_RANDOM 1
#define INTF_ID_CSID   2
#define INTF_ID_IPV4   3

#define INTF_ID_SECRET_MIN_LEN 16
#define INTF_ID_SECRET_MAX_LEN 128

static int conf_check_exists;
static int conf_intf_id = INTF_ID_FIXED;
static uint64_t conf_intf_id_val = 1;
static int conf_peer_intf_id = INTF_ID_FIXED;
static uint64_t conf_peer_intf_id_val = 2;
static int conf_accept_peer_intf_id;
static const char *conf_peer_intf_id_secret;

static struct ipv6cp_option_t *ipaddr_init(struct ppp_ipv6cp_t *ipv6cp);
static void ipaddr_free(struct ppp_ipv6cp_t *ipv6cp, struct ipv6cp_option_t *opt);
static int ipaddr_send_conf_req(struct ppp_ipv6cp_t *ipv6cp, struct ipv6cp_option_t *opt, uint8_t *ptr);
static int ipaddr_send_conf_nak(struct ppp_ipv6cp_t *ipv6cp, struct ipv6cp_option_t *opt, uint8_t *ptr);
static int ipaddr_recv_conf_req(struct ppp_ipv6cp_t *ipv6cp, struct ipv6cp_option_t *opt, uint8_t *ptr);
//static int ipaddr_recv_conf_ack(struct ppp_ipv6cp_t *ipv6cp, struct ipv6cp_option_t *opt, uint8_t *ptr);
static void ipaddr_print(void (*print)(const char *fmt,...),struct ipv6cp_option_t*, uint8_t *ptr);
static void put_ipv6_item(struct ap_session *ses, struct ipv6db_item_t *ip6);

struct ipaddr_option_t
{
	struct ipv6cp_option_t opt;
	unsigned int started:1;
	struct ppp_t *ppp;
};

static struct ipv6cp_option_handler_t ipaddr_opt_hnd =
{
	.init          = ipaddr_init,
	.send_conf_req = ipaddr_send_conf_req,
	.send_conf_nak = ipaddr_send_conf_nak,
	.recv_conf_req = ipaddr_recv_conf_req,
	.free          = ipaddr_free,
	.print         = ipaddr_print,
};

/* ipdb backend used for generating a link-local address when all other
 * backends (like radius and ipv6pool) failed to assign IPv6 addresses.
 * This backend isn't registered to ipdb as it's only used as a fallback
 * during IPv6CP negociation.
 */
static struct ipdb_t ipv6db = {
	.put_ipv6 = put_ipv6_item
};

static void put_ipv6_item(struct ap_session *ses, struct ipv6db_item_t *ip6)
{
	_free(ip6);
}

static int gen_ipv6_item(struct ap_session *ses)
{
	struct ipv6db_item_t *ip6 = NULL;

	ip6 = _malloc(sizeof(*ip6));
	if (ip6 == NULL) {
		log_ppp_warn("ppp: allocation of IPv6 address failed\n");
		return -1;
	}

	memset(ip6, 0, sizeof(*ip6));
	ip6->owner = &ipv6db;
	ip6->intf_id = 0;
	ip6->peer_intf_id = 0;
	INIT_LIST_HEAD(&ip6->addr_list);

	ses->ipv6 = ip6;

	return 0;
}

static struct ipv6cp_option_t *ipaddr_init(struct ppp_ipv6cp_t *ipv6cp)
{
	struct ipaddr_option_t *ipaddr_opt = _malloc(sizeof(*ipaddr_opt));

	memset(ipaddr_opt, 0, sizeof(*ipaddr_opt));

	ipaddr_opt->opt.id = CI_INTFID;
	ipaddr_opt->opt.len = 10;
	ipaddr_opt->ppp = ipv6cp->ppp;

	return &ipaddr_opt->opt;
}

static void ipaddr_free(struct ppp_ipv6cp_t *ipv6cp, struct ipv6cp_option_t *opt)
{
	struct ipaddr_option_t *ipaddr_opt=container_of(opt,typeof(*ipaddr_opt),opt);

	_free(ipaddr_opt);
}

static int check_exists(struct ppp_t *self_ppp)
{
	struct ap_session *ses;
	struct ipv6db_addr_t *a1, *a2;
	int r = 0;

	pthread_rwlock_rdlock(&ses_lock);
	list_for_each_entry(ses, &ses_list, entry) {
		if (ses->terminating)
			continue;
		if (!ses->ipv6)
			continue;
		if (ses == &self_ppp->ses)
			continue;

		list_for_each_entry(a1, &ses->ipv6->addr_list, entry) {
			list_for_each_entry(a2, &self_ppp->ses.ipv6->addr_list, entry) {
				if (a1->addr.s6_addr32[0] == a2->addr.s6_addr32[0] &&
						a1->addr.s6_addr32[1] == a2->addr.s6_addr32[1]) {
					log_ppp_warn("ppp: requested IPv6 address already assigned to %s\n", ses->ifname);
					r = 1;
					goto out;
				}
			}
		}
	}
out:
	pthread_rwlock_unlock(&ses_lock);

	return r;
}

static uint64_t generate_intf_id(struct ppp_t *ppp)
{
	uint64_t id = 0;

	switch (conf_intf_id) {
		case INTF_ID_FIXED:
			return conf_intf_id_val;
			break;
		//case INTF_ID_RANDOM:
		default:
			read(urandom_fd, &id, 8);
			break;
	}

	return id;
}

static int is_iid_all_zero(const uint8_t iid[8])
{
	int i;

	for (i = 0; i < 8; ++i) {
		if (iid[i])
			return 0;
	}

	return 1;
}

static int is_printable_ascii_secret(const char *secret)
{
	const unsigned char *p;

	if (!secret || !*secret)
		return 0;

	for (p = (const unsigned char *)secret; *p; ++p) {
		/* ASCII range 0x21 to 0x7E are printable non-whitespace characters */
		if (*p <= 0x20 || *p > 0x7e)
			return 0;
	}

	return 1;
}

/* RFC 5072 Section 4.1 requires the Interface-Identifier "u" bit to be
 * zero unless an EUI-48/EUI-64-derived identifier is used for the remote
 * peer. RFC 4291 requires avoiding the all-zero IID.
 */
static void normalize_opaque_iid(uint8_t iid[8])
{
	/* Clear EUI-64 U/L bit (0x02 in the first octet). */
	iid[0] &= 0xfd;

	if (is_iid_all_zero(iid))
		iid[7] = 1;
}

static uint64_t generate_csid_intf_id(struct ppp_t *ppp)
{
	const char *csid;
	const char *ctrl_name = "unknown";
	unsigned int ctrl_type = 0;
	char type_buf[12];
	char *csid_norm = NULL;
	char *context = NULL;
	const char *prefix = "ctrl-type=";
	const char *middle = "|ctrl-name=";
	const char *suffix = "|csid=";
	unsigned char digest[EVP_MAX_MD_SIZE];
	unsigned int digest_len = 0;
	uint8_t iid_bytes[8];
	uint64_t id = 0;
	size_t csid_len;
	size_t ctrl_name_len;
	size_t context_len;
	int secret_len;
	int i;
	int n;

	if (!ppp || !ppp->ses.ctrl)
		return 0;

	csid = ppp->ses.ctrl->calling_station_id;
	if (!csid || !*csid)
		return 0;

	if (!conf_peer_intf_id_secret || !*conf_peer_intf_id_secret)
		return 0;

	ctrl_type = ppp->ses.ctrl->type;
	if (ppp->ses.ctrl->name)
		ctrl_name = ppp->ses.ctrl->name;

	n = snprintf(type_buf, sizeof(type_buf), "%u", ctrl_type);
	if (n <= 0 || n >= (int)sizeof(type_buf))
		return 0;

	csid_len = strlen(csid);
	ctrl_name_len = strlen(ctrl_name);
	context_len = strlen(prefix) + strlen(type_buf) + strlen(middle) + ctrl_name_len + strlen(suffix) + csid_len;

	csid_norm = _malloc(csid_len + 1);
	if (!csid_norm)
		return 0;

	for (i = 0; i < (int)csid_len; ++i)
		csid_norm[i] = tolower((unsigned char)csid[i]);
	csid_norm[csid_len] = '\0';

	context = _malloc(context_len + 1);
	if (!context)
		goto out;

	n = snprintf(context, context_len + 1, "%s%s%s%s%s%s", prefix, type_buf, middle, ctrl_name, suffix, csid_norm);
	if (n <= 0 || (size_t)n != context_len)
		goto out;

	secret_len = (int)strlen(conf_peer_intf_id_secret);

	if (!HMAC(EVP_sha256(), conf_peer_intf_id_secret, secret_len,
			(const unsigned char *)context, context_len, digest, &digest_len))
		goto out;

	if (digest_len < sizeof(iid_bytes))
		goto out;

	memcpy(iid_bytes, digest, sizeof(iid_bytes));
	normalize_opaque_iid(iid_bytes);
	memcpy(&id, iid_bytes, sizeof(id));

out:
	_free(context);
	_free(csid_norm);
	return id;
}

static uint64_t generate_peer_intf_id(struct ppp_t *ppp)
{
	char str[4];
	int i;
	unsigned int n;
	union {
		uint64_t intf_id;
		uint16_t addr16[4];
	} u = { .intf_id = 0 };

	switch (conf_peer_intf_id) {
		case INTF_ID_FIXED:
			return conf_peer_intf_id_val;
			break;
		case INTF_ID_RANDOM:
			read(urandom_fd, &u, sizeof(u));
			break;
		case INTF_ID_CSID:
			u.intf_id = generate_csid_intf_id(ppp);
			break;
		case INTF_ID_IPV4:
			if (ppp->ses.ipv4) {
				for (i = 0; i < 4; i++) {
					sprintf(str, "%i", (ppp->ses.ipv4->peer_addr >> (i*8)) & 0xff);
					sscanf(str, "%x", &n);
					u.addr16[i] = htons(n);
				}
			} else
				return 0;
	}

	return u.intf_id;
}

static int alloc_ip(struct ppp_t *ppp)
{
	ppp->ses.ipv6 = ipdb_get_ipv6(&ppp->ses);
	if (!ppp->ses.ipv6) {
		if (gen_ipv6_item(&ppp->ses) < 0) {
			log_ppp_warn("ppp: no free IPv6 address\n");
			return IPV6CP_OPT_CLOSE;
		}
	}

	if (!ppp->ses.ipv6->intf_id)
		ppp->ses.ipv6->intf_id = generate_intf_id(ppp);

	if (conf_check_exists && check_exists(ppp))
		return IPV6CP_OPT_FAIL;

	return 0;
}

static int ipaddr_send_conf_req(struct ppp_ipv6cp_t *ipv6cp, struct ipv6cp_option_t *opt, uint8_t *ptr)
{
	struct ipaddr_option_t *ipaddr_opt = container_of(opt, typeof(*ipaddr_opt), opt);
	struct ipv6cp_opt64_t *opt64 = (struct ipv6cp_opt64_t *)ptr;
	int r;

	if (!ipv6cp->ppp->ses.ipv6) {
		r = alloc_ip(ipv6cp->ppp);
		if (r)
			return r;
	}

	opt64->hdr.id = CI_INTFID;
	opt64->hdr.len = 10;
	opt64->val = ipv6cp->ppp->ses.ipv6->intf_id;
	return 10;
}

static int ipaddr_send_conf_nak(struct ppp_ipv6cp_t *ipv6cp, struct ipv6cp_option_t *opt, uint8_t *ptr)
{
	struct ipaddr_option_t *ipaddr_opt = container_of(opt, typeof(*ipaddr_opt), opt);
	struct ipv6cp_opt64_t *opt64 = (struct ipv6cp_opt64_t *)ptr;
	opt64->hdr.id = CI_INTFID;
	opt64->hdr.len = 10;
	opt64->val = ipv6cp->ppp->ses.ipv6->peer_intf_id;
	return 10;
}

static int ipaddr_recv_conf_req(struct ppp_ipv6cp_t *ipv6cp, struct ipv6cp_option_t *opt, uint8_t *ptr)
{
	struct ipaddr_option_t *ipaddr_opt = container_of(opt, typeof(*ipaddr_opt), opt);
	struct ipv6cp_opt64_t *opt64 = (struct ipv6cp_opt64_t* )ptr;
	int r;

	if (opt64->hdr.len != 10)
		return IPV6CP_OPT_REJ;

	if (!ipv6cp->ppp->ses.ipv6) {
		r = alloc_ip(ipv6cp->ppp);
		if (r)
			return r;
	}

	if (conf_accept_peer_intf_id && opt64->val)
		ipv6cp->ppp->ses.ipv6->peer_intf_id = opt64->val;
	else if (!ipv6cp->ppp->ses.ipv6->peer_intf_id) {
		ipv6cp->ppp->ses.ipv6->peer_intf_id = generate_peer_intf_id(ipv6cp->ppp);
		if (!ipv6cp->ppp->ses.ipv6->peer_intf_id)
			return IPV6CP_OPT_TERMACK;
	}

	if (opt64->val && ipv6cp->ppp->ses.ipv6->peer_intf_id == opt64->val && opt64->val != ipv6cp->ppp->ses.ipv6->intf_id) {
		ipv6cp->delay_ack = ccp_ipcp_started(ipv6cp->ppp);
		ipaddr_opt->started = 1;
		return IPV6CP_OPT_ACK;
	}

	return IPV6CP_OPT_NAK;
}

static void ipaddr_print(void (*print)(const char *fmt,...), struct ipv6cp_option_t *opt, uint8_t *ptr)
{
	struct ipaddr_option_t *ipaddr_opt = container_of(opt, typeof(*ipaddr_opt), opt);
	struct ipv6cp_opt64_t *opt64 = (struct ipv6cp_opt64_t *)ptr;
	struct in6_addr a;

	if (ptr)
		*(uint64_t *)(a.s6_addr + 8) = opt64->val;
	else
		*(uint64_t *)(a.s6_addr + 8) = ipaddr_opt->ppp->ses.ipv6->intf_id;

	print("<addr %x:%x:%x:%x>", ntohs(a.s6_addr16[4]), ntohs(a.s6_addr16[5]), ntohs(a.s6_addr16[6]), ntohs(a.s6_addr16[7]));
}

static uint64_t parse_intfid(const char *opt)
{
	union {
		uint64_t u64;
		uint16_t u16[4];
	} u;

	unsigned int n[4];
	int i;

	if (sscanf(opt, "%x:%x:%x:%x", &n[0], &n[1], &n[2], &n[3]) != 4)
		goto err;

	for (i = 0; i < 4; i++) {
		if (n[i] > 0xffff)
			goto err;
		u.u16[i] = htons(n[i]);
	}

	return u.u64;

err:
	log_error("ppp:ipv6cp: failed to parse intf-id '%s'\n", opt);
	conf_intf_id = INTF_ID_RANDOM;
	return 0;
}

static void load_config(void)
{
	const char *opt;
	size_t secret_len;

	opt = conf_get_opt("ppp", "check-ip");
	if (!opt)
		opt = conf_get_opt("common", "check-ip");
	if (opt && atoi(opt) >= 0)
		conf_check_exists = atoi(opt) > 0;

	opt = conf_get_opt("ppp", "ipv6-intf-id");
	if (opt) {
		if (!strcmp(opt, "random"))
			conf_intf_id = INTF_ID_RANDOM;
		else {
			conf_intf_id = INTF_ID_FIXED;
			conf_intf_id_val = parse_intfid(opt);
		}
	}

	opt = conf_get_opt("ppp", "ipv6-peer-intf-id");
	if (opt) {
		if (!strcmp(opt, "random"))
			conf_peer_intf_id = INTF_ID_RANDOM;
		else if (!strcmp(opt, "calling-sid"))
			conf_peer_intf_id = INTF_ID_CSID;
		else if (!strcmp(opt, "ipv4"))
			conf_peer_intf_id = INTF_ID_IPV4;
		else {
			conf_peer_intf_id = INTF_ID_FIXED;
			conf_peer_intf_id_val = parse_intfid(opt);
		}
	}

	conf_peer_intf_id_secret = conf_get_opt("ppp", "ipv6-peer-intf-id-secret");
	if (conf_peer_intf_id_secret && *conf_peer_intf_id_secret) {
		secret_len = strlen(conf_peer_intf_id_secret);
		if (secret_len < INTF_ID_SECRET_MIN_LEN ||
		    secret_len > INTF_ID_SECRET_MAX_LEN) {
			log_error("ppp: ipv6-peer-intf-id-secret length must be between %d and %d characters\n",
				INTF_ID_SECRET_MIN_LEN, INTF_ID_SECRET_MAX_LEN);
			conf_peer_intf_id_secret = NULL;
		} else if (!is_printable_ascii_secret(conf_peer_intf_id_secret)) {
			log_error("ppp: ipv6-peer-intf-id-secret must contain only printable non-whitespace ASCII characters\n");
			conf_peer_intf_id_secret = NULL;
		}
	}
	if (conf_peer_intf_id == INTF_ID_CSID && (!conf_peer_intf_id_secret || !*conf_peer_intf_id_secret))
		log_error("ppp: ipv6-peer-intf-id=calling-sid requires non-empty ipv6-peer-intf-id-secret\n");

	opt = conf_get_opt("ppp", "ipv6-accept-peer-intf-id");
	if (opt)
		conf_accept_peer_intf_id = atoi(opt);
}

static void init()
{
	if (sock6_fd < 0)
		return;

	ipv6cp_option_register(&ipaddr_opt_hnd);
	load_config();
	triton_event_register_handler(EV_CONFIG_RELOAD, (triton_event_func)load_config);
}

DEFINE_INIT(5, init);

