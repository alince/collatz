// Standalone C23 multi-step 2-adic Hensel branch-and-bound accelerator.
// Compiles cleanly with bundled Clang 23 (-std=c23 -O3 -nostdlib -shared).
// 100% bit-for-bit identical to _run_hensel_root_chunk and _run_windowed_hensel_chunk
// in collatz_analysis/goal_extensions.py, with deterministic max_budget timeout guard.

#if defined(_WIN32)
#define HENSEL_EXPORT __declspec(dllexport)
#else
#define HENSEL_EXPORT __attribute__((visibility("default")))
#endif

typedef __UINT64_TYPE__ u64;
typedef __INT64_TYPE__ i64;
typedef unsigned __int128 u128;
typedef unsigned _BitInt(256) u256;
typedef unsigned _BitInt(384) u384;
typedef unsigned _BitInt(640) u640;

typedef struct {
    u64 w[6];
} u384_io;

typedef struct {
    int k1;
    int pad;
    u384_io lo1;
    u384_io hi1;
    u384_io u_min;
    u384_io u_max;
} BandIO;

typedef struct {
    u384_io w_lo;
    u384_io w_hi;
} StepBoundIO;

static inline u384 load_u384(const u384_io *src) {
    return ((u384)src->w[0])
         | ((u384)src->w[1] << 64)
         | ((u384)src->w[2] << 128)
         | ((u384)src->w[3] << 192)
         | ((u384)src->w[4] << 256)
         | ((u384)src->w[5] << 320);
}

static inline void store_u384(u384_io *dst, u384 val) {
    dst->w[0] = (u64)val;
    dst->w[1] = (u64)(val >> 64);
    dst->w[2] = (u64)(val >> 128);
    dst->w[3] = (u64)(val >> 192);
    dst->w[4] = (u64)(val >> 256);
    dst->w[5] = (u64)(val >> 320);
}

static inline int bit_length_384(u384 x) {
    u64 w5 = (u64)(x >> 320);
    if (w5) return 384 - __builtin_clzll(w5);
    u64 w4 = (u64)(x >> 256);
    if (w4) return 320 - __builtin_clzll(w4);
    u64 w3 = (u64)(x >> 192);
    if (w3) return 256 - __builtin_clzll(w3);
    u64 w2 = (u64)(x >> 128);
    if (w2) return 192 - __builtin_clzll(w2);
    u64 w1 = (u64)(x >> 64);
    if (w1) return 128 - __builtin_clzll(w1);
    u64 w0 = (u64)x;
    if (w0) return 64 - __builtin_clzll(w0);
    return 0;
}

static inline int bit_length_640(u640 x) {
    if ((x >> 384) == 0) return bit_length_384((u384)x);
    u64 w9 = (u64)(x >> 576);
    if (w9) return 640 - __builtin_clzll(w9);
    u64 w8 = (u64)(x >> 512);
    if (w8) return 576 - __builtin_clzll(w8);
    u64 w7 = (u64)(x >> 448);
    if (w7) return 512 - __builtin_clzll(w7);
    u64 w6 = (u64)(x >> 384);
    return 448 - __builtin_clzll(w6);
}

static inline int ctz_384(u384 x) {
    u64 w0 = (u64)x;
    if (w0) return __builtin_ctzll(w0);
    u64 w1 = (u64)(x >> 64);
    if (w1) return 64 + __builtin_ctzll(w1);
    u64 w2 = (u64)(x >> 128);
    if (w2) return 128 + __builtin_ctzll(w2);
    u64 w3 = (u64)(x >> 192);
    if (w3) return 192 + __builtin_ctzll(w3);
    u64 w4 = (u64)(x >> 256);
    if (w4) return 256 + __builtin_ctzll(w4);
    u64 w5 = (u64)(x >> 320);
    if (w5) return 320 + __builtin_ctzll(w5);
    return 384;
}

static inline int ctz_640(u640 x) {
    int clow = ctz_384((u384)x);
    if (clow < 384) return clow;
    u64 w6 = (u64)(x >> 384);
    if (w6) return 384 + __builtin_ctzll(w6);
    u64 w7 = (u64)(x >> 448);
    if (w7) return 448 + __builtin_ctzll(w7);
    u64 w8 = (u64)(x >> 512);
    if (w8) return 512 + __builtin_ctzll(w8);
    u64 w9 = (u64)(x >> 576);
    if (w9) return 576 + __builtin_ctzll(w9);
    return 640;
}

static inline u384 shl384(u384 x, int s) {
    if (s <= 0) return x;
    if (s >= 384) return (u384)0;
    return x << s;
}

static inline u384 shr384(u384 x, int s) {
    if (s <= 0) return x;
    if (s >= 384) return (u384)0;
    return x >> s;
}

static inline u384 shr640_clamp384(u640 x, int s) {
    if (s >= 640) return (u384)0;
    u640 v = (s > 0) ? (x >> s) : x;
    if ((v >> 384) != 0) return ~(u384)0;
    return (u384)v;
}

static inline int bit_length_fast(u384 x) {
    if ((x >> 192) == 0) {
        u64 w2 = (u64)(x >> 128);
        if (w2) return 192 - __builtin_clzll(w2);
        u64 w1 = (u64)(x >> 64);
        if (w1) return 128 - __builtin_clzll(w1);
        u64 w0 = (u64)x;
        if (w0) return 64 - __builtin_clzll(w0);
        return 0;
    }
    return bit_length_384(x);
}

static u384 g_p3[243];
static u640 g_p3_640[365];
static u384 g_inv3[360];
static u384 g_inv3_full[6000];
static u384 g_mask384[385];
static u128 g_mask128[129];
static int g_tables_ready = 0;

static void ensure_tables(void) {
    if (g_tables_ready) return;
    u384 mod_mask = (((u384)1) << 320) - 1;
    u384 inv3_full_one = (u384)0xaaaaaaaaaaaaaaabULL;
    for (int i = 0; i < 5; i++) {
        inv3_full_one = inv3_full_one * ((u384)2 - (u384)3 * inv3_full_one);
    }
    u384 inv3_one = inv3_full_one & mod_mask;
    g_p3[0] = 1;
    for (int i = 1; i < 243; i++) {
        g_p3[i] = g_p3[i - 1] * (u384)3;
    }
    g_p3_640[0] = 1;
    for (int i = 1; i < 365; i++) {
        g_p3_640[i] = g_p3_640[i - 1] * (u640)3;
    }

    g_inv3[0] = 1;
    for (int i = 1; i < 360; i++) {
        g_inv3[i] = (g_inv3[i - 1] * inv3_one) & mod_mask;
    }
    g_inv3_full[0] = 1;
    for (int i = 1; i < 6000; i++) {
        g_inv3_full[i] = g_inv3_full[i - 1] * inv3_full_one;
    }
    g_mask384[0] = 0;
    for (int i = 1; i < 384; i++) {
        g_mask384[i] = (((u384)1) << i) - 1;
    }
    g_mask384[384] = ~(u384)0;
    g_mask128[0] = 0;
    for (int i = 1; i < 128; i++) {
        g_mask128[i] = (((u128)1) << i) - 1;
    }
    g_mask128[128] = ~(u128)0;
    g_tables_ready = 1;
}

static inline u384 next_odd_spiral_minimum(u384 x) {
    u384 xp1 = x + 1;
    int k = ctz_384(xp1);
    u384 u = shr384(xp1, k);
    u384 ev = g_p3[k] * u - 1;
    int ell = ctz_384(ev);
    return shr384(ev, ell);
}

static inline u384 next_odd_spiral_minimum_safe(u384 x) {
    u384 xp1 = x + 1;
    int k = ctz_384(xp1);
    u384 u = shr384(xp1, k);
    if (k <= 238 && (xp1 >> 238) == 0) {
        u384 ev = g_p3[k] * u - 1;
        int ell = ctz_384(ev);
        return shr384(ev, ell);
    }
    u640 ev640 = g_p3_640[k] * (u640)u - (u640)1;
    int ell = ctz_640(ev640);
    return shr640_clamp384(ev640, ell);
}

static inline u640 mul_p3_u640(int kd, u384 u) {
    if (kd <= 80 && (u >> 128) == 0) {
        return (u640)((u256)(u128)g_p3[kd] * (u256)(u128)u);
    }
    return g_p3_640[kd] * (u640)u;
}

static inline u384 mul_p3_u(int kd, u384 u) {
    if (kd <= 80 && (u >> 128) == 0) {
        return (u384)((u256)(u128)g_p3[kd] * (u256)(u128)u);
    }
    if (kd <= 160 && (u >> 256) == 0 && (kd <= 80 || (u >> 192) == 0)) {
        // 3^80 < 2^127; for kd <= 160, if 1.585*kd + bl(u) < 255, u256 is exact:
        if (kd * 820 + bit_length_fast(u) * 512 < 255 * 512) {
            return (u384)((u256)g_p3[kd] * (u256)u);
        }
    }
    return g_p3[kd] * u;
}

static inline u384 mul_mod_loc(u384 a, u384 b, int loc_bits, u384 loc_mask) {
    if (loc_bits <= 256) {
        return (u384)((u256)a * (u256)b) & loc_mask;
    }
    return (a * b) & loc_mask;
}

#define MAX_SURVIVORS 4096

typedef struct {
    u384 n0_threshold;
    u384 b_lo;
    u384 b_hi;
    u384 two_b_lo;
    u384 two_b_hi;
    u384 mod_mask;
    u384 loc_mask;
    u384 l_eff;
    u384 u_eff;
    int u_eff_bl;
    int loc_bits;
    int b_lo_bl;
    int b_hi_bl;
    int cur_r;
    int max_r_verify;
    const int *kd_lo;
    const int *kd_hi;
    // Windowed fields
    int is_windowed;
    u384 step_w_lo[16];
    u384 step_w_hi[16];
    int step_w_lo_bl[16];
    int step_w_hi_bl[16];
    const int *step_kd_lo[16];
    // Two-vertex (x_(1), x_(2)) budget-splitting fields
    int is_two_vertex;
    int bridge_to_x2;
    u384 x2_lo;
    u384 x2_hi;
    int x2_lo_bl;
    int x2_hi_bl;
    const int *kd_lo_bridge;

    u64 nodes;
    u64 leaf_ops;
    u64 max_budget;
    int aborted;
    int max_survivors;
    int num_survivors;
    u384_io *out_survivors;
} HenselCtx;

static inline int eq_u384_io(const u384_io *a, u384 b) {
    return load_u384(a) == b;
}

static void add_survivor(HenselCtx *ctx, u384 z) {
    for (int i = 0; i < ctx->num_survivors; i++) {
        if (eq_u384_io(&ctx->out_survivors[i], z)) return;
    }
    if (ctx->num_survivors < ctx->max_survivors) {
        store_u384(&ctx->out_survivors[ctx->num_survivors++], z);
    } else {
        ctx->aborted = 2;
    }
}

static void verify_z1(HenselCtx *ctx, u384 z) {
    if (ctx->aborted) return;
    if (((u64)z & 1ULL) == 0ULL || z <= ctx->n0_threshold) return;
    if (ctx->is_two_vertex) {
        if (ctx->bridge_to_x2 == 3 || ctx->bridge_to_x2 == 5) {
            u384 cur = z;
            for (int step = 0; step <= ctx->max_r_verify; step++) {
                cur = next_odd_spiral_minimum_safe(cur);
                if (cur >= ctx->x2_lo && cur <= ctx->x2_hi && cur != z && (ctx->bridge_to_x2 == 3 || step >= 1)) {
                    add_survivor(ctx, z);
                    return;
                }
                if (cur > ctx->b_hi || cur < ctx->b_lo) return;
            }
            return;
        }
        u384 min_allowed = z + 2;
        if (ctx->x2_lo > min_allowed) min_allowed = ctx->x2_lo;
        u384 cur = z;
        int is_br = (ctx->bridge_to_x2 >= 1 && ctx->bridge_to_x2 <= 3);
        for (int step = 0; step <= ctx->max_r_verify; step++) {
            cur = next_odd_spiral_minimum_safe(cur);
            if (cur < min_allowed) return;
            if (is_br) {
                if (cur <= ctx->x2_hi && (ctx->bridge_to_x2 == 1 || step >= 1)) {
                    add_survivor(ctx, z);
                    return;
                }
                if (cur > ctx->b_hi || cur < ctx->b_lo) return;
            } else {
                if (cur > ctx->b_hi) {
                    if (ctx->bridge_to_x2 == 4 || step >= 1) add_survivor(ctx, z);
                    return;
                }
                if (cur < ctx->b_lo) return;
            }
        }
        return;
    }
    u384 cur = z;
    for (int step = 0; step <= ctx->max_r_verify; step++) {
        cur = next_odd_spiral_minimum(cur);
        if (cur > ctx->b_hi) {
            if (step >= 1) {
                add_survivor(ctx, z);
            }
            return;
        }
        if (cur < ctx->b_lo) {
            return;
        }
    }
}

static void eval_leaf_general(
    HenselCtx *ctx,
    int k_exp,
    int w_exp,
    u384 g_val,
    u384 hi_z,
    u384 l1_p1,
    u384 u1_p1,
    int k_coll,
    u384 leaf_mask
) {
    u384 hi_p1 = hi_z + 1;
    u384 lo_p1 = (u384)2;
    if (w_exp < 200 && (w_exp * 2 + ctx->u_eff_bl < 375) && ((g_val >> 375) == 0)) {
        u384 z_aff_hi = shr384(mul_p3_u(w_exp, ctx->u_eff) + g_val, k_exp);
        if (z_aff_hi < 2) return;
        if (z_aff_hi < hi_p1) {
            if (((u64)z_aff_hi & 1ULL) != 0ULL) z_aff_hi -= 1;
            if (z_aff_hi < 2) return;
            hi_p1 = z_aff_hi;
        }
        u384 z_aff_lo = shr384(mul_p3_u(w_exp, ctx->l_eff) + g_val + g_mask384[k_exp], k_exp);
        if (z_aff_lo > hi_p1) return;
        if (z_aff_lo > lo_p1) {
            if (((u64)z_aff_lo & 1ULL) != 0ULL) z_aff_lo += 1;
            if (z_aff_lo > hi_p1) return;
            lo_p1 = z_aff_lo;
        }
    }
    int b_hi_cur = bit_length_fast(hi_p1);
    int kd_start = ctx->kd_hi[b_hi_cur];
    if (kd_start > b_hi_cur) return;
    u384 span = u1_p1 - l1_p1;
    u128 span_128 = (u128)span;
    u384 p3k_g_run = g_p3[kd_start] * g_val;

    for (int kd = kd_start; kd <= b_hi_cur; kd++) {
        int s_kkd = k_exp + kd;
        if (s_kkd >= k_coll) {
            ctx->leaf_ops++;
            if (s_kkd <= 128 && k_coll <= 127) {
                u128 mc_m1 = g_mask128[s_kkd];
                u128 rc128 = (((u128)0 - (u128)g_val) * (u128)g_inv3[w_exp]) & mc_m1;
                u128 rem128 = (rc128 - (u128)l1_p1) & mc_m1;
                if (rem128 <= span_128) {
                    u384 mc = g_mask384[s_kkd] + 1;
                    u384 f = l1_p1 + (u384)rem128;
                    while (f <= u1_p1) {
                        verify_z1(ctx, f - 1);
                        f += mc;
                    }
                }
            } else {
                u384 mc_m1 = g_mask384[s_kkd];
                u384 mc = mc_m1 + 1;
                u384 rc = (((u384)0 - g_val) * g_inv3[w_exp]) & mc_m1;
                u384 diff_c = (rc - l1_p1) & mc_m1;
                if (diff_c <= span) {
                    u384 f = l1_p1 + diff_c;
                    while (f <= u1_p1) {
                        verify_z1(ctx, f - 1);
                        f += mc;
                    }
                }
            }
            break;
        }
        u384 p3k_g = p3k_g_run;
        p3k_g_run += (p3k_g_run << 1);

        u384 u_max = shr384(hi_p1, kd);
        if (u_max == 0) continue;
        if (((u64)u_max & 1ULL) == 0ULL) u_max -= 1;
        if (u_max < 1) continue;
        u384 u_min_l = shr384(lo_p1 + g_mask384[kd], kd);
        if (u_min_l > u_max) continue;

        u384 ev_max = mul_p3_u(kd, u_max) - 1;
        if (ev_max <= ctx->two_b_hi) continue;
        int w_n = w_exp + kd;
        u384 inv_wn = g_inv3[w_n];
        int ld_lim = bit_length_fast(ev_max) - ctx->b_hi_bl + 2;

        if (k_coll <= 127) {
            u128 sh_128 = ((u128)1) << s_kkd;
            u128 base_diff_128 = ((sh_128 - (u128)p3k_g) * (u128)inv_wn) - (u128)l1_p1;
            u128 inv_sh_128 = (u128)inv_wn << (s_kkd + 1);
            u384 z_ev = ev_max >> 1;
            for (int ld = 1; ld <= ld_lim; ld++, z_ev >>= 1) {
                if (z_ev <= ctx->b_hi) break;
                int k_n = s_kkd + ld;
                if (k_n >= k_coll) {
                    ctx->leaf_ops++;
                    u128 ml_m1 = g_mask128[k_n];
                    u128 rem128 = base_diff_128 & ml_m1;
                    if (rem128 <= span_128) {
                        u384 ml = (u384)ml_m1 + 1;
                        u384 f = l1_p1 + (u384)rem128;
                        while (f <= u1_p1) {
                            verify_z1(ctx, f - 1);
                            f += ml;
                        }
                    }
                    break;
                }
                ctx->leaf_ops++;
                u128 me_m1 = g_mask128[k_n + 1];
                u128 rem_e = (base_diff_128 - inv_sh_128) & me_m1;
                inv_sh_128 <<= 1;
                if (rem_e <= span_128) {
                    u384 me = (u384)me_m1 + 1;
                    u384 f = l1_p1 + (u384)rem_e;
                    while (f <= u1_p1) {
                        verify_z1(ctx, f - 1);
                        f += me;
                    }
                }
            }
        } else {
            u384 sh_kkd = g_mask384[s_kkd] + 1;
            u384 base_r = ((sh_kkd - p3k_g) * inv_wn) & leaf_mask;
            u384 z_ev = ev_max >> 1;
            for (int ld = 1; ld <= ld_lim; ld++, z_ev >>= 1) {
                if (z_ev <= ctx->b_hi) break;
                int k_n = s_kkd + ld;
                if (k_n >= k_coll) {
                    ctx->leaf_ops++;
                    u384 ml_m1 = g_mask384[k_n];
                    u384 diff_l = (base_r - l1_p1) & ml_m1;
                    if (diff_l <= span) {
                        u384 ml = ml_m1 + 1;
                        u384 f = l1_p1 + diff_l;
                        while (f <= u1_p1) {
                            verify_z1(ctx, f - 1);
                            f += ml;
                        }
                    }
                    break;
                }
                ctx->leaf_ops++;
                u384 me_m1 = g_mask384[k_n + 1];
                u384 re = (base_r - shl384(inv_wn, k_n)) & me_m1;
                u384 diff_e = (re - l1_p1) & me_m1;
                if (diff_e <= span) {
                    u384 me = me_m1 + 1;
                    u384 f = l1_p1 + diff_e;
                    while (f <= u1_p1) {
                        verify_z1(ctx, f - 1);
                        f += me;
                    }
                }
            }
        }
    }
}

static void dfs_standard(
    HenselCtx *ctx,
    int depth,
    int k_exp,
    int w_exp,
    u384 g_val,
    u384 lo_z,
    u384 hi_z,
    u384 l1_p1,
    u384 u1_p1,
    int k_coll
) {
    if (ctx->aborted) return;
    ctx->nodes++;
    if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
        ctx->aborted = 1;
        return;
    }
    if (k_exp + 1 >= k_coll) {
        ctx->leaf_ops++;
        u384 mod = shl384((u384)1, k_exp + 1);
        u384 mod_m1 = mod - 1;
        u384 r = (((mod - g_val) & mod_m1) * g_inv3[w_exp]) & mod_m1;
        u384 f = l1_p1 + ((r - l1_p1) & mod_m1);
        while (f <= u1_p1) {
            verify_z1(ctx, f - 1);
            f += mod;
        }
        return;
    }
    if (depth == ctx->cur_r) {
        eval_leaf_general(ctx, k_exp, w_exp, g_val, hi_z, l1_p1, u1_p1, k_coll, ctx->mod_mask);
        return;
    }

    u384 hi_p1 = hi_z + 1;
    u384 lo_p1 = lo_z + 1;
    if (w_exp < 200 && (w_exp * 2 + ctx->u_eff_bl < 375) && ((g_val >> 375) == 0)) {
        u384 z_aff_hi = shr384(mul_p3_u(w_exp, ctx->u_eff) + g_val, k_exp);
        if (z_aff_hi < lo_p1) return;
        if (z_aff_hi < hi_p1) {
            if (((u64)z_aff_hi & 1ULL) != 0ULL) z_aff_hi -= 1;
            if (z_aff_hi < lo_p1) return;
            hi_p1 = z_aff_hi;
        }
        u384 z_aff_lo = shr384(mul_p3_u(w_exp, ctx->l_eff) + g_val + g_mask384[k_exp], k_exp);
        if (z_aff_lo > hi_p1) return;
        if (z_aff_lo > lo_p1) {
            if (((u64)z_aff_lo & 1ULL) != 0ULL) z_aff_lo += 1;
            if (z_aff_lo > hi_p1) return;
            lo_p1 = z_aff_lo;
        }
    }
    int b_hi_cur = bit_length_fast(hi_p1);
    int next_is_leaf = (depth + 1 == ctx->cur_r);
    u384 span = u1_p1 - l1_p1;
    int kd_start = ctx->kd_lo[b_hi_cur];
    u384 p3k_g_run = (kd_start <= b_hi_cur) ? (g_p3[kd_start] * g_val) : (u384)0;

    for (int kd = kd_start; kd <= b_hi_cur; kd++) {
        if (k_exp + kd >= k_coll) {
            ctx->leaf_ops++;
            if (k_exp + kd <= 128 && k_coll <= 127) {
                u128 mc_m1 = g_mask128[k_exp + kd];
                u128 rc128 = (((u128)0 - (u128)g_val) * (u128)g_inv3[w_exp]) & mc_m1;
                u128 rem128 = (rc128 - (u128)l1_p1) & mc_m1;
                if (rem128 <= (u128)span) {
                    u384 mc = g_mask384[k_exp + kd] + 1;
                    u384 f = l1_p1 + (u384)rem128;
                    while (f <= u1_p1) {
                        verify_z1(ctx, f - 1);
                        f += mc;
                    }
                }
            } else {
                u384 mc_m1 = g_mask384[k_exp + kd];
                u384 mc = mc_m1 + 1;
                u384 rc = mul_mod_loc((u384)0 - g_val, g_inv3[w_exp], k_exp + kd, mc_m1);
                u384 f = l1_p1 + ((rc - l1_p1) & mc_m1);
                while (f <= u1_p1) {
                    verify_z1(ctx, f - 1);
                    f += mc;
                }
            }
            break;
        }
        u384 p3k_g = p3k_g_run;
        p3k_g_run += (p3k_g_run << 1);

        u384 u_min = shr384(lo_p1 + g_mask384[kd], kd);
        if (u_min < 1) u_min = 1;
        if (((u64)u_min & 1ULL) == 0ULL) u_min += 1;
        u384 u_max = shr384(hi_p1, kd);
        if (u_max < u_min) continue;
        if (((u64)u_max & 1ULL) == 0ULL) u_max -= 1;
        if (u_min > u_max) continue;

        int w_n = w_exp + kd;
        int s_kkd = k_exp + kd;
        u384 ev_max = mul_p3_u(kd, u_max) - 1;
        if (ev_max < ctx->two_b_lo) continue;
        u384 ev_min = mul_p3_u(kd, u_min) - 1;
        int ld_start = bit_length_fast(ev_min) - ctx->b_hi_bl;
        if (ld_start < 1) ld_start = 1;
        if (shr384(ev_min, ld_start) > ctx->b_hi) ld_start += 1;
        int ld_end = bit_length_fast(ev_max) - ctx->b_lo_bl + 1;
        if (ld_start > ld_end) continue;
        u384 z_next_max = shr384(ev_max, ld_start);
        if (z_next_max < ctx->b_lo) continue;

        u384 inv_wn = g_inv3[w_n];
        u384 sh_kkd = g_mask384[s_kkd] + 1;

        if (next_is_leaf) {
            int k_kd = k_exp + kd;
            if (k_coll <= 127) {
                u128 base_diff_128 = (((u128)sh_kkd - (u128)p3k_g) * (u128)inv_wn) - (u128)l1_p1;
                u128 inv_sh_128 = (u128)inv_wn << (k_kd + ld_start);
                u128 span_128 = (u128)span;
                for (int ld = ld_start; ld <= ld_end; ld++, z_next_max >>= 1) {
                    if (z_next_max < ctx->b_lo) break;
                    int k_n = k_kd + ld;
                    if (k_n >= k_coll) {
                        ctx->leaf_ops++;
                        u128 ml_m1 = g_mask128[k_n];
                        u128 rem128 = base_diff_128 & ml_m1;
                        if (rem128 <= span_128) {
                            u384 ml = (u384)ml_m1 + 1;
                            u384 f = l1_p1 + (u384)rem128;
                            while (f <= u1_p1) {
                                verify_z1(ctx, f - 1);
                                f += ml;
                            }
                        }
                        break;
                    }
                    u128 cur_inv_128 = inv_sh_128;
                    inv_sh_128 <<= 1;
                    int b_nhi = (z_next_max >= ctx->b_hi) ? ctx->b_hi_bl : bit_length_fast(z_next_max + 1);
                    int ks = ctx->kd_hi[b_nhi];
                    if (ks > b_nhi) continue;
                    int s_exp = k_n + ks;
                    if (s_exp >= k_coll) {
                        ctx->leaf_ops++;
                        if (s_exp <= 128) {
                            u128 diff128 = (base_diff_128 - cur_inv_128) & g_mask128[s_exp];
                            if (diff128 <= span_128) {
                                u384 mc = g_mask384[s_exp] + 1;
                                u384 f = l1_p1 + (u384)diff128;
                                while (f <= u1_p1) {
                                    verify_z1(ctx, f - 1);
                                    f += mc;
                                }
                            }
                        } else {
                            if ((base_diff_128 - cur_inv_128) <= span_128) {
                                u384 base_r = mul_mod_loc(sh_kkd - p3k_g, inv_wn, ctx->loc_bits, ctx->loc_mask);
                                u384 base_diff = (base_r - l1_p1) & ctx->loc_mask;
                                u384 mask_c = g_mask384[s_exp];
                                u384 diff_c = (base_diff - shl384(inv_wn, k_n)) & mask_c;
                                if (diff_c <= span) {
                                    u384 mc = mask_c + 1;
                                    u384 f = l1_p1 + diff_c;
                                    while (f <= u1_p1) {
                                        verify_z1(ctx, f - 1);
                                        f += mc;
                                    }
                                }
                            }
                        }
                    } else {
                        u384 n_hi = (z_next_max >= ctx->b_hi)
                            ? ctx->b_hi
                            : ((((u64)z_next_max & 1ULL) != 0ULL) ? z_next_max : (z_next_max - 1));
                        u384 g_n = p3k_g + sh_kkd * g_mask384[ld];
                        eval_leaf_general(ctx, k_n, w_n, g_n, n_hi, l1_p1, u1_p1, k_coll, ctx->mod_mask);
                    }
                }
            } else {
                u384 base_r = mul_mod_loc(sh_kkd - p3k_g, inv_wn, ctx->loc_bits, ctx->loc_mask);
                u384 base_diff = (base_r - l1_p1) & ctx->loc_mask;
                u384 inv_sh = shl384(inv_wn, k_kd + ld_start);
                for (int ld = ld_start; ld <= ld_end; ld++, z_next_max >>= 1) {
                    if (z_next_max < ctx->b_lo) break;
                    int k_n = k_kd + ld;
                    if (k_n >= k_coll) {
                        ctx->leaf_ops++;
                        u384 ml_m1 = g_mask384[k_n];
                        if ((base_diff & ml_m1) <= span) {
                            u384 ml = ml_m1 + 1;
                            u384 f = l1_p1 + (base_diff & ml_m1);
                            while (f <= u1_p1) {
                                verify_z1(ctx, f - 1);
                                f += ml;
                            }
                        }
                        break;
                    }
                    u384 cur_inv_sh = inv_sh;
                    inv_sh <<= 1;
                    int b_nhi = (z_next_max >= ctx->b_hi) ? ctx->b_hi_bl : bit_length_fast(z_next_max + 1);
                    int ks = ctx->kd_hi[b_nhi];
                    if (ks > b_nhi) continue;
                    if (k_n + ks >= k_coll) {
                        ctx->leaf_ops++;
                        u384 mask_c = g_mask384[k_n + ks];
                        u384 diff_c = (base_diff - cur_inv_sh) & mask_c;
                        if (diff_c <= span) {
                            u384 mc = mask_c + 1;
                            u384 f = l1_p1 + diff_c;
                            while (f <= u1_p1) {
                                verify_z1(ctx, f - 1);
                                f += mc;
                            }
                        }
                    } else {
                        u384 n_hi = (z_next_max >= ctx->b_hi)
                            ? ctx->b_hi
                            : ((((u64)z_next_max & 1ULL) != 0ULL) ? z_next_max : (z_next_max - 1));
                        u384 g_n = p3k_g + sh_kkd * g_mask384[ld];
                        eval_leaf_general(ctx, k_n, w_n, g_n, n_hi, l1_p1, u1_p1, k_coll, ctx->mod_mask);
                    }
                }
            }
            if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
                ctx->aborted = 1;
                return;
            }
        } else {
            u384 z_next_min = shr384(ev_min, ld_start);
            for (int ld = ld_start; ld <= ld_end; ld++, z_next_max >>= 1, z_next_min >>= 1) {
                if (z_next_max < ctx->b_lo) break;
                if (z_next_min > ctx->b_hi) continue;
                int k_n = k_exp + kd + ld;
                if (k_n >= k_coll) {
                    ctx->leaf_ops++;
                    if (k_n <= 128 && k_coll <= 127) {
                        u128 bd128 = (((u128)sh_kkd - (u128)p3k_g) * (u128)inv_wn - (u128)l1_p1) & g_mask128[k_n];
                        if (bd128 <= (u128)span) {
                            u384 ml = g_mask384[k_n] + 1;
                            u384 f = l1_p1 + (u384)bd128;
                            while (f <= u1_p1) {
                                verify_z1(ctx, f - 1);
                                f += ml;
                            }
                        }
                    } else {
                        u384 base_r = mul_mod_loc(sh_kkd - p3k_g, inv_wn, ctx->loc_bits, ctx->loc_mask);
                        u384 base_diff = (base_r - l1_p1) & ctx->loc_mask;
                        u384 ml_m1 = g_mask384[k_n];
                        if ((base_diff & ml_m1) <= span) {
                            u384 ml = ml_m1 + 1;
                            u384 f = l1_p1 + (base_diff & ml_m1);
                            while (f <= u1_p1) {
                                verify_z1(ctx, f - 1);
                                f += ml;
                            }
                        }
                    }
                    break;
                }
                u384 n_hi = (z_next_max >= ctx->b_hi)
                    ? ctx->b_hi
                    : ((((u64)z_next_max & 1ULL) != 0ULL) ? z_next_max : (z_next_max - 1));
                u384 n_lo = (z_next_min <= ctx->b_lo) ? ctx->b_lo : (z_next_min | (u384)1);
                if (n_lo <= n_hi) {
                    int b_nhi_nxt = bit_length_fast(n_hi + 1);
                    int ks_nxt = ctx->kd_lo[b_nhi_nxt];
                    if (ks_nxt > b_nhi_nxt) continue;
                    int s_exp_nxt = k_n + ks_nxt;
                    if (s_exp_nxt >= k_coll) {
                        ctx->leaf_ops++;
                        if (s_exp_nxt <= 128 && k_coll <= 127) {
                            u128 bd128 = ((u128)sh_kkd - (u128)p3k_g) * (u128)inv_wn - (u128)l1_p1;
                            u128 diff128 = (bd128 - ((u128)inv_wn << k_n)) & g_mask128[s_exp_nxt];
                            if (diff128 <= (u128)span) {
                                u384 mc = g_mask384[s_exp_nxt] + 1;
                                u384 f = l1_p1 + (u384)diff128;
                                while (f <= u1_p1) {
                                    verify_z1(ctx, f - 1);
                                    f += mc;
                                }
                            }
                        } else {
                            u384 base_r = mul_mod_loc(sh_kkd - p3k_g, inv_wn, ctx->loc_bits, ctx->loc_mask);
                            u384 base_diff = (base_r - l1_p1) & ctx->loc_mask;
                            u384 mask_c = g_mask384[s_exp_nxt];
                            u384 diff_c = (base_diff - shl384(inv_wn, k_n)) & mask_c;
                            if (diff_c <= span) {
                                u384 mc = mask_c + 1;
                                u384 f = l1_p1 + diff_c;
                                while (f <= u1_p1) {
                                    verify_z1(ctx, f - 1);
                                    f += mc;
                                }
                            }
                        }
                        continue;
                    }
                    u384 g_n = p3k_g + sh_kkd * g_mask384[ld];
                    dfs_standard(ctx, depth + 1, k_n, w_n, g_n, n_lo, n_hi, l1_p1, u1_p1, k_coll);
                    if (ctx->aborted) return;
                }
            }
        }
    }
}

static void dfs_windowed(
    HenselCtx *ctx,
    int depth,
    int k_exp,
    int w_exp,
    u384 g_val,
    u384 lo_z,
    u384 hi_z,
    u384 l1_p1,
    u384 u1_p1,
    int k_coll
) {
    if (ctx->aborted) return;
    ctx->nodes++;
    if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
        ctx->aborted = 1;
        return;
    }
    if (k_exp + 1 >= k_coll) {
        ctx->leaf_ops++;
        u384 mod = shl384((u384)1, k_exp + 1);
        u384 mod_m1 = mod - 1;
        u384 r = (((mod - g_val) & mod_m1) * g_inv3[w_exp]) & mod_m1;
        u384 f = l1_p1 + ((r - l1_p1) & mod_m1);
        while (f <= u1_p1) {
            verify_z1(ctx, f - 1);
            f += mod;
        }
        return;
    }
    if (depth == ctx->cur_r) {
        eval_leaf_general(ctx, k_exp, w_exp, g_val, hi_z, l1_p1, u1_p1, k_coll, ctx->loc_mask);
        return;
    }

    u384 w_lo_nxt = ctx->step_w_lo[depth];
    u384 w_hi_nxt = ctx->step_w_hi[depth];
    u384 two_w_lo_nxt = 2 * w_lo_nxt;
    int w_lo_nxt_bl = ctx->step_w_lo_bl[depth];
    int w_hi_nxt_bl = ctx->step_w_hi_bl[depth];
    const int *kd_lo_step = ctx->step_kd_lo[depth];

    u384 hi_p1 = hi_z + 1;
    u384 lo_p1 = lo_z + 1;
    if (w_exp < 200 && (w_exp * 2 + ctx->u_eff_bl < 375) && ((g_val >> 375) == 0)) {
        u384 z_aff_hi = shr384(mul_p3_u(w_exp, ctx->u_eff) + g_val, k_exp);
        if (z_aff_hi < lo_p1) return;
        if (z_aff_hi < hi_p1) {
            if (((u64)z_aff_hi & 1ULL) != 0ULL) z_aff_hi -= 1;
            if (z_aff_hi < lo_p1) return;
            hi_p1 = z_aff_hi;
        }
        u384 z_aff_lo = shr384(mul_p3_u(w_exp, ctx->l_eff) + g_val + g_mask384[k_exp], k_exp);
        if (z_aff_lo > hi_p1) return;
        if (z_aff_lo > lo_p1) {
            if (((u64)z_aff_lo & 1ULL) != 0ULL) z_aff_lo += 1;
            if (z_aff_lo > hi_p1) return;
            lo_p1 = z_aff_lo;
        }
    }
    int b_hi_cur = bit_length_fast(hi_p1);
    int next_is_leaf = (depth + 1 == ctx->cur_r);
    u384 span = u1_p1 - l1_p1;
    int kd_start = kd_lo_step[b_hi_cur];
    u384 p3k_g_run = (kd_start <= b_hi_cur) ? (g_p3[kd_start] * g_val) : (u384)0;

    for (int kd = kd_start; kd <= b_hi_cur; kd++) {
        if (k_exp + kd >= k_coll) {
            ctx->leaf_ops++;
            if (k_exp + kd <= 128 && k_coll <= 127) {
                u128 mc_m1 = g_mask128[k_exp + kd];
                u128 rc128 = (((u128)0 - (u128)g_val) * (u128)g_inv3[w_exp]) & mc_m1;
                u128 rem128 = (rc128 - (u128)l1_p1) & mc_m1;
                if (rem128 <= (u128)span) {
                    u384 mc = g_mask384[k_exp + kd] + 1;
                    u384 f = l1_p1 + (u384)rem128;
                    while (f <= u1_p1) {
                        verify_z1(ctx, f - 1);
                        f += mc;
                    }
                }
            } else {
                u384 mc_m1 = g_mask384[k_exp + kd];
                u384 mc = mc_m1 + 1;
                u384 rc = mul_mod_loc((u384)0 - g_val, g_inv3[w_exp], k_exp + kd, mc_m1);
                u384 f = l1_p1 + ((rc - l1_p1) & mc_m1);
                while (f <= u1_p1) {
                    verify_z1(ctx, f - 1);
                    f += mc;
                }
            }
            break;
        }
        u384 p3k_g = p3k_g_run;
        p3k_g_run += (p3k_g_run << 1);

        u384 u_min = shr384(lo_p1 + g_mask384[kd], kd);
        if (u_min < 1) u_min = 1;
        if (((u64)u_min & 1ULL) == 0ULL) u_min += 1;
        u384 u_max = shr384(hi_p1, kd);
        if (u_max < u_min) continue;
        if (((u64)u_max & 1ULL) == 0ULL) u_max -= 1;
        if (u_min > u_max) continue;

        int w_n = w_exp + kd;
        int s_kkd = k_exp + kd;
        u384 ev_max = mul_p3_u(kd, u_max) - 1;
        if (ev_max < two_w_lo_nxt) continue;
        u384 ev_min = mul_p3_u(kd, u_min) - 1;
        int ld_start = bit_length_fast(ev_min) - w_hi_nxt_bl;
        if (ld_start < 1) ld_start = 1;
        if (shr384(ev_min, ld_start) > w_hi_nxt) ld_start += 1;
        int ld_end = bit_length_fast(ev_max) - w_lo_nxt_bl + 1;
        if (ld_start > ld_end) continue;
        u384 z_next_max = shr384(ev_max, ld_start);
        if (z_next_max < w_lo_nxt) continue;

        u384 inv_wn = g_inv3[w_n];
        u384 sh_kkd = g_mask384[s_kkd] + 1;

        if (next_is_leaf) {
            int k_kd = k_exp + kd;
            u384 z_next_min = shr384(ev_min, ld_start);
            if (k_coll <= 127) {
                u128 base_diff_128 = (((u128)sh_kkd - (u128)p3k_g) * (u128)inv_wn) - (u128)l1_p1;
                u128 inv_sh_128 = (u128)inv_wn << (k_kd + ld_start);
                u128 span_128 = (u128)span;
                for (int ld = ld_start; ld <= ld_end; ld++, z_next_max >>= 1, z_next_min >>= 1) {
                    if (z_next_max < w_lo_nxt) break;
                    if (z_next_min > w_hi_nxt) {
                        inv_sh_128 <<= 1;
                        continue;
                    }
                    int k_n = k_kd + ld;
                    if (k_n >= k_coll) {
                        ctx->leaf_ops++;
                        u128 ml_m1 = g_mask128[k_n];
                        u128 rem128 = base_diff_128 & ml_m1;
                        if (rem128 <= span_128) {
                            u384 ml = (u384)ml_m1 + 1;
                            u384 f = l1_p1 + (u384)rem128;
                            while (f <= u1_p1) {
                                verify_z1(ctx, f - 1);
                                f += ml;
                            }
                        }
                        break;
                    }
                    u128 cur_inv_128 = inv_sh_128;
                    inv_sh_128 <<= 1;
                    u384 z_eff_max = (z_next_max >= w_hi_nxt) ? w_hi_nxt : z_next_max;
                    int b_nhi = (z_eff_max >= ctx->b_hi) ? ctx->b_hi_bl : bit_length_fast(z_eff_max + 1);
                    int ks = ctx->kd_hi[b_nhi];
                    if (ks > b_nhi) continue;
                    int s_exp = k_n + ks;
                    if (s_exp >= k_coll) {
                        ctx->leaf_ops++;
                        if (s_exp <= 128) {
                            u128 diff128 = (base_diff_128 - cur_inv_128) & g_mask128[s_exp];
                            if (diff128 <= span_128) {
                                u384 mc = g_mask384[s_exp] + 1;
                                u384 f = l1_p1 + (u384)diff128;
                                while (f <= u1_p1) {
                                    verify_z1(ctx, f - 1);
                                    f += mc;
                                }
                            }
                        } else {
                            if ((base_diff_128 - cur_inv_128) <= span_128) {
                                u384 base_r = mul_mod_loc(sh_kkd - p3k_g, inv_wn, ctx->loc_bits, ctx->loc_mask);
                                u384 base_diff = (base_r - l1_p1) & ctx->loc_mask;
                                u384 mask_c = g_mask384[s_exp];
                                u384 diff_c = (base_diff - shl384(inv_wn, k_n)) & mask_c;
                                if (diff_c <= span) {
                                    u384 mc = mask_c + 1;
                                    u384 f = l1_p1 + diff_c;
                                    while (f <= u1_p1) {
                                        verify_z1(ctx, f - 1);
                                        f += mc;
                                    }
                                }
                            }
                        }
                    } else {
                        u384 n_hi = (((u64)z_eff_max & 1ULL) != 0ULL) ? z_eff_max : (z_eff_max - 1);
                        if (n_hi >= w_lo_nxt) {
                            u384 g_n = p3k_g + sh_kkd * g_mask384[ld];
                            eval_leaf_general(ctx, k_n, w_n, g_n, n_hi, l1_p1, u1_p1, k_coll, ctx->loc_mask);
                        }
                    }
                }
            } else {
                u384 base_r = mul_mod_loc(sh_kkd - p3k_g, inv_wn, ctx->loc_bits, ctx->loc_mask);
                u384 base_diff = (base_r - l1_p1) & ctx->loc_mask;
                u384 inv_sh = shl384(inv_wn, k_kd + ld_start);
                for (int ld = ld_start; ld <= ld_end; ld++, z_next_max >>= 1, z_next_min >>= 1) {
                    if (z_next_max < w_lo_nxt) break;
                    if (z_next_min > w_hi_nxt) {
                        inv_sh <<= 1;
                        continue;
                    }
                    int k_n = k_kd + ld;
                    if (k_n >= k_coll) {
                        ctx->leaf_ops++;
                        u384 ml_m1 = g_mask384[k_n];
                        if ((base_diff & ml_m1) <= span) {
                            u384 ml = ml_m1 + 1;
                            u384 f = l1_p1 + (base_diff & ml_m1);
                            while (f <= u1_p1) {
                                verify_z1(ctx, f - 1);
                                f += ml;
                            }
                        }
                        break;
                    }
                    u384 cur_inv_sh = inv_sh;
                    inv_sh <<= 1;
                    u384 z_eff_max = (z_next_max >= w_hi_nxt) ? w_hi_nxt : z_next_max;
                    int b_nhi = (z_eff_max >= ctx->b_hi) ? ctx->b_hi_bl : bit_length_fast(z_eff_max + 1);
                    int ks = ctx->kd_hi[b_nhi];
                    if (ks > b_nhi) continue;
                    if (k_n + ks >= k_coll) {
                        ctx->leaf_ops++;
                        u384 mask_c = g_mask384[k_n + ks];
                        u384 diff_c = (base_diff - cur_inv_sh) & mask_c;
                        if (diff_c <= span) {
                            u384 mc = mask_c + 1;
                            u384 f = l1_p1 + diff_c;
                            while (f <= u1_p1) {
                                verify_z1(ctx, f - 1);
                                f += mc;
                            }
                        }
                    } else {
                        u384 n_hi = (((u64)z_eff_max & 1ULL) != 0ULL) ? z_eff_max : (z_eff_max - 1);
                        if (n_hi >= w_lo_nxt) {
                            u384 g_n = p3k_g + sh_kkd * g_mask384[ld];
                            eval_leaf_general(ctx, k_n, w_n, g_n, n_hi, l1_p1, u1_p1, k_coll, ctx->loc_mask);
                        }
                    }
                }
            }
            if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
                ctx->aborted = 1;
                return;
            }
        } else {
            const int *next_kd_lo = ctx->step_kd_lo[depth + 1];
            u384 z_next_min = shr384(ev_min, ld_start);
            for (int ld = ld_start; ld <= ld_end; ld++, z_next_max >>= 1, z_next_min >>= 1) {
                if (z_next_max < w_lo_nxt) break;
                if (z_next_min > w_hi_nxt) continue;
                int k_n = k_exp + kd + ld;
                if (k_n >= k_coll) {
                    ctx->leaf_ops++;
                    if (k_n <= 128 && k_coll <= 127) {
                        u128 bd128 = (((u128)sh_kkd - (u128)p3k_g) * (u128)inv_wn - (u128)l1_p1) & g_mask128[k_n];
                        if (bd128 <= (u128)span) {
                            u384 ml = g_mask384[k_n] + 1;
                            u384 f = l1_p1 + (u384)bd128;
                            while (f <= u1_p1) {
                                verify_z1(ctx, f - 1);
                                f += ml;
                            }
                        }
                    } else {
                        u384 base_r = mul_mod_loc(sh_kkd - p3k_g, inv_wn, ctx->loc_bits, ctx->loc_mask);
                        u384 base_diff = (base_r - l1_p1) & ctx->loc_mask;
                        u384 ml_m1 = g_mask384[k_n];
                        if ((base_diff & ml_m1) <= span) {
                            u384 ml = ml_m1 + 1;
                            u384 f = l1_p1 + (base_diff & ml_m1);
                            while (f <= u1_p1) {
                                verify_z1(ctx, f - 1);
                                f += ml;
                            }
                        }
                    }
                    break;
                }
                u384 n_hi = (z_next_max >= w_hi_nxt)
                    ? w_hi_nxt
                    : ((((u64)z_next_max & 1ULL) != 0ULL) ? z_next_max : (z_next_max - 1));
                u384 n_lo = (z_next_min <= w_lo_nxt) ? w_lo_nxt : (z_next_min | (u384)1);
                if (n_lo <= n_hi) {
                    int b_nhi_nxt = bit_length_fast(n_hi + 1);
                    int ks_nxt = next_kd_lo[b_nhi_nxt];
                    if (ks_nxt > b_nhi_nxt) continue;
                    int s_exp_nxt = k_n + ks_nxt;
                    if (s_exp_nxt >= k_coll) {
                        ctx->leaf_ops++;
                        if (s_exp_nxt <= 128 && k_coll <= 127) {
                            u128 bd128 = ((u128)sh_kkd - (u128)p3k_g) * (u128)inv_wn - (u128)l1_p1;
                            u128 diff128 = (bd128 - ((u128)inv_wn << k_n)) & g_mask128[s_exp_nxt];
                            if (diff128 <= (u128)span) {
                                u384 mc = g_mask384[s_exp_nxt] + 1;
                                u384 f = l1_p1 + (u384)diff128;
                                while (f <= u1_p1) {
                                    verify_z1(ctx, f - 1);
                                    f += mc;
                                }
                            }
                        } else {
                            u384 base_r = mul_mod_loc(sh_kkd - p3k_g, inv_wn, ctx->loc_bits, ctx->loc_mask);
                            u384 base_diff = (base_r - l1_p1) & ctx->loc_mask;
                            u384 mask_c = g_mask384[s_exp_nxt];
                            u384 diff_c = (base_diff - shl384(inv_wn, k_n)) & mask_c;
                            if (diff_c <= span) {
                                u384 mc = mask_c + 1;
                                u384 f = l1_p1 + diff_c;
                                while (f <= u1_p1) {
                                    verify_z1(ctx, f - 1);
                                    f += mc;
                                }
                            }
                        }
                        continue;
                    }
                    u384 g_n = p3k_g + sh_kkd * g_mask384[ld];
                    dfs_windowed(ctx, depth + 1, k_n, w_n, g_n, n_lo, n_hi, l1_p1, u1_p1, k_coll);
                    if (ctx->aborted) return;
                }
            }
        }
    }
}

HENSEL_EXPORT int run_hensel_standard_c(
    const u384_io *n0_io,
    const u384_io *b1_io,
    const u384_io *b2_io,
    int max_r,
    int num_bands,
    const BandIO *bands,
    const int *kd_lo,
    const int *kd_hi,
    u64 max_budget,
    u64 *out_nodes,
    u64 *out_leaf_ops,
    int *out_num_survivors,
    u384_io *out_survivors
) {
    ensure_tables();
    HenselCtx ctx;
    ctx.n0_threshold = load_u384(n0_io);
    u384 b1_val = load_u384(b1_io);
    u384 b2_val = load_u384(b2_io);
    ctx.b_lo = b1_val + 1;
    ctx.b_hi = b2_val;
    ctx.two_b_lo = 2 * ctx.b_lo;
    ctx.two_b_hi = 2 * ctx.b_hi;
    ctx.b_lo_bl = bit_length_384(ctx.b_lo);
    ctx.b_hi_bl = bit_length_384(ctx.b_hi);
    ctx.mod_mask = (((u384)1) << 320) - 1;
    ctx.loc_mask = ctx.mod_mask;
    ctx.max_r_verify = max_r;
    ctx.kd_lo = kd_lo;
    ctx.kd_hi = kd_hi;
    ctx.is_windowed = 0;
    ctx.is_two_vertex = 0;
    ctx.bridge_to_x2 = 0;
    ctx.kd_lo_bridge = 0;
    ctx.nodes = 0;
    ctx.leaf_ops = 0;
    ctx.max_budget = max_budget;
    ctx.aborted = 0;
    ctx.max_survivors = MAX_SURVIVORS;
    ctx.num_survivors = 0;
    ctx.out_survivors = out_survivors;

    for (int cur_r = 1; cur_r <= max_r; cur_r++) {
        ctx.cur_r = cur_r;
        for (int b = 0; b < num_bands; b++) {
            int k1 = bands[b].k1;
            u384 lo1 = load_u384(&bands[b].lo1);
            u384 hi1 = load_u384(&bands[b].hi1);
            u384 u_min = load_u384(&bands[b].u_min);
            u384 u_max = load_u384(&bands[b].u_max);
            u384 l1_p1 = lo1 + 1;
            u384 u1_p1 = hi1 + 1;
            u384 l_eff = shl384(u_min, k1);
            if (l_eff > l1_p1) l1_p1 = l_eff;
            u384 u_eff = shl384(u_max, k1);
            if (u_eff < u1_p1) u1_p1 = u_eff;
            if (l1_p1 > u1_p1) continue;
            ctx.l_eff = l1_p1;
            ctx.u_eff = u1_p1;
            ctx.u_eff_bl = bit_length_384(u1_p1);
            int k_coll = bit_length_384(u1_p1 - l1_p1);
            if (k_coll < 1) k_coll = 1;
            int loc_bits = k_coll + ctx.b_hi_bl + 8;
            if (loc_bits > 320) loc_bits = 320;
            ctx.loc_bits = loc_bits;
            ctx.loc_mask = g_mask384[loc_bits];

            u384 ev_min = g_p3[k1] * u_min - 1;
            u384 ev_max = g_p3[k1] * u_max - 1;
            if ((ev_max >> 1) > b2_val) {
                return -3; // Direct r=0 jump over B2
            }
            int ld_start = bit_length_384(ev_min) - ctx.b_hi_bl;
            if (ld_start < 1) ld_start = 1;
            if (shr384(ev_min, ld_start) > ctx.b_hi) ld_start += 1;
            int l1_end = bit_length_384(ev_max) - ctx.b_lo_bl + 2;
            if (l1_end < ld_start) l1_end = ld_start;
            for (int l1 = ld_start; l1 <= l1_end; l1++) {
                u384 z2_max = shr384(ev_max, l1);
                if (z2_max < ctx.b_lo) break;
                u384 z2_min = shr384(ev_min, l1);
                if (z2_min > ctx.b_hi) continue;
                u384 z2_min_odd = z2_min | (u384)1;
                u384 n_lo = (ctx.b_lo >= z2_min_odd) ? ctx.b_lo : z2_min_odd;
                u384 z2_max_odd = (((u64)z2_max & 1ULL) != 0ULL) ? z2_max : (z2_max - 1);
                u384 n_hi = (ctx.b_hi <= z2_max_odd) ? ctx.b_hi : z2_max_odd;
                if (n_lo <= n_hi) {
                    u384 g1 = shl384((u384)1, k1) * (shl384((u384)1, l1) - 1);
                    dfs_standard(&ctx, 1, k1 + l1, k1, g1, n_lo, n_hi, l1_p1, u1_p1, k_coll);
                    if (ctx.aborted) break;
                }
            }
            if (ctx.aborted) break;
        }
        if (ctx.aborted) break;
    }

    *out_nodes = ctx.nodes;
    *out_leaf_ops = ctx.leaf_ops;
    *out_num_survivors = ctx.num_survivors;
    return ctx.aborted;
}

HENSEL_EXPORT int run_hensel_windowed_c(
    const u384_io *n0_io,
    const u384_io *b1_io,
    const u384_io *b2_io,
    int exact_r,
    const StepBoundIO *step_bounds,
    int num_bands,
    const BandIO *bands,
    const int *kd_lo_flat,
    int kd_stride,
    const int *kd_hi,
    u64 max_budget,
    u64 *out_nodes,
    u64 *out_leaf_ops,
    int *out_num_survivors,
    u384_io *out_survivors
) {
    ensure_tables();
    if (exact_r < 1 || exact_r > 15) return -4;
    HenselCtx ctx;
    ctx.n0_threshold = load_u384(n0_io);
    u384 b1_val = load_u384(b1_io);
    u384 b2_val = load_u384(b2_io);
    ctx.b_lo = b1_val + 1;
    ctx.b_hi = b2_val;
    ctx.two_b_lo = 2 * ctx.b_lo;
    ctx.two_b_hi = 2 * ctx.b_hi;
    ctx.b_lo_bl = bit_length_384(ctx.b_lo);
    ctx.b_hi_bl = bit_length_384(ctx.b_hi);
    ctx.mod_mask = (((u384)1) << 320) - 1;
    ctx.loc_mask = ctx.mod_mask;
    ctx.cur_r = exact_r;
    ctx.max_r_verify = exact_r;
    ctx.kd_lo = 0;
    ctx.kd_hi = kd_hi;
    ctx.is_windowed = 1;
    ctx.is_two_vertex = 0;
    ctx.bridge_to_x2 = 0;
    ctx.kd_lo_bridge = 0;
    ctx.nodes = 0;
    ctx.leaf_ops = 0;
    ctx.max_budget = max_budget;
    ctx.aborted = 0;
    ctx.max_survivors = MAX_SURVIVORS;
    ctx.num_survivors = 0;
    ctx.out_survivors = out_survivors;

    for (int d = 0; d < exact_r; d++) {
        ctx.step_w_lo[d] = load_u384(&step_bounds[d].w_lo);
        ctx.step_w_hi[d] = load_u384(&step_bounds[d].w_hi);
        ctx.step_w_lo_bl[d] = bit_length_384(ctx.step_w_lo[d]);
        ctx.step_w_hi_bl[d] = bit_length_384(ctx.step_w_hi[d]);
        ctx.step_kd_lo[d] = kd_lo_flat + d * kd_stride;
    }

    u384 w_lo_0 = ctx.step_w_lo[0];
    u384 w_hi_0 = ctx.step_w_hi[0];
    int w_lo_0_bl = ctx.step_w_lo_bl[0];
    int w_hi_0_bl = ctx.step_w_hi_bl[0];

    for (int b = 0; b < num_bands; b++) {
        int k1 = bands[b].k1;
        u384 lo1 = load_u384(&bands[b].lo1);
        u384 hi1 = load_u384(&bands[b].hi1);
        u384 u_min = load_u384(&bands[b].u_min);
        u384 u_max = load_u384(&bands[b].u_max);
        u384 l1_p1 = lo1 + 1;
        u384 u1_p1 = hi1 + 1;
        u384 l_eff = shl384(u_min, k1);
        if (l_eff > l1_p1) l1_p1 = l_eff;
        u384 u_eff = shl384(u_max, k1);
        if (u_eff < u1_p1) u1_p1 = u_eff;
        if (l1_p1 > u1_p1) continue;
        ctx.l_eff = l1_p1;
        ctx.u_eff = u1_p1;
        ctx.u_eff_bl = bit_length_384(u1_p1);
        int k_coll = bit_length_384(u1_p1 - l1_p1);
        if (k_coll < 1) k_coll = 1;
        int loc_bits = k_coll + ctx.b_hi_bl + 8;
        if (loc_bits > 320) loc_bits = 320;
        ctx.loc_bits = loc_bits;
        ctx.loc_mask = g_mask384[loc_bits];

        u384 ev_min = g_p3[k1] * u_min - 1;
        u384 ev_max = g_p3[k1] * u_max - 1;
        if ((ev_max >> 1) > b2_val) {
            return -3;
        }
        int ld_start = bit_length_384(ev_min) - w_hi_0_bl;
        if (ld_start < 1) ld_start = 1;
        if (shr384(ev_min, ld_start) > w_hi_0) ld_start += 1;
        int l1_end = bit_length_384(ev_max) - w_lo_0_bl + 2;
        if (l1_end < ld_start) l1_end = ld_start;
        for (int l1 = ld_start; l1 <= l1_end; l1++) {
            u384 z2_max = shr384(ev_max, l1);
            if (z2_max < w_lo_0) break;
            u384 z2_min = shr384(ev_min, l1);
            if (z2_min > w_hi_0) continue;
            u384 z2_min_odd = z2_min | (u384)1;
            u384 n_lo = (w_lo_0 >= z2_min_odd) ? w_lo_0 : z2_min_odd;
            u384 z2_max_odd = (((u64)z2_max & 1ULL) != 0ULL) ? z2_max : (z2_max - 1);
            u384 n_hi = (w_hi_0 <= z2_max_odd) ? w_hi_0 : z2_max_odd;
            if (n_lo <= n_hi) {
                u384 g1 = shl384((u384)1, k1) * (shl384((u384)1, l1) - 1);
                dfs_windowed(&ctx, 1, k1 + l1, k1, g1, n_lo, n_hi, l1_p1, u1_p1, k_coll);
                if (ctx.aborted) break;
            }
        }
        if (ctx.aborted) break;
    }

    *out_nodes = ctx.nodes;
    *out_leaf_ops = ctx.leaf_ops;
    *out_num_survivors = ctx.num_survivors;
    return ctx.aborted;
}

static inline u384 p3_mod384(int k) {
    return (k < 243) ? g_p3[k] : (u384)g_p3_640[k];
}

static inline void test_congruence_two_vertex(
    HenselCtx *ctx,
    u384 r_mod,
    int m_exp,
    u384 l1_p1,
    u384 u1_p1,
    u384 span
) {
    ctx->leaf_ops++;
    if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
        ctx->aborted = 1;
        return;
    }
    int m = (m_exp <= 380) ? m_exp : 380;
    u384 m_m1 = g_mask384[m];
    u384 diff = (r_mod - l1_p1) & m_m1;
    if (diff <= span) {
        u384 step = m_m1 + 1;
        u384 f = l1_p1 + diff;
        while (f <= u1_p1) {
            if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
                ctx->aborted = 1;
                return;
            }
            verify_z1(ctx, f - 1);
            ctx->leaf_ops++;
            if (ctx->aborted) return;
            f += step;
        }
    }
}

static inline int tighten_affine_two_vertex(
    const HenselCtx *ctx,
    int k_exp,
    int w_exp,
    u384 g_val,
    int g_exact,
    u384 *lo_p1,
    u384 *hi_p1
) {
    if (g_exact && w_exp <= 360 && (w_exp * 820 + ctx->u_eff_bl * 512 < 635 * 512)) {
        u384 z_aff_hi = shr640_clamp384(mul_p3_u640(w_exp, ctx->u_eff) + (u640)g_val, k_exp);
        if (z_aff_hi < *lo_p1) return 0;
        if (z_aff_hi < *hi_p1) {
            if (((u64)z_aff_hi & 1ULL) != 0ULL) z_aff_hi -= 1;
            if (z_aff_hi < *lo_p1) return 0;
            *hi_p1 = z_aff_hi;
        }
        u384 z_aff_lo = shr640_clamp384(
            mul_p3_u640(w_exp, ctx->l_eff) + (u640)g_val + (u640)g_mask384[k_exp],
            k_exp
        );
        if (z_aff_lo > *hi_p1) return 0;
        if (z_aff_lo > *lo_p1) {
            if (((u64)z_aff_lo & 1ULL) != 0ULL) z_aff_lo += 1;
            if (z_aff_lo > *hi_p1) return 0;
            *lo_p1 = z_aff_lo;
        }
    }
    return 1;
}

static void eval_leaf_exit_two_vertex(
    HenselCtx *ctx,
    int k_exp,
    int w_exp,
    u384 g_val,
    int g_exact,
    u384 lo_z,
    u384 hi_z,
    u384 l1_p1,
    u384 u1_p1,
    int k_coll
) {
    u384 hi_p1 = hi_z + 1;
    u384 lo_p1 = lo_z + 1;
    if (!tighten_affine_two_vertex(ctx, k_exp, w_exp, g_val, g_exact, &lo_p1, &hi_p1)) return;
    int b_hi_cur = bit_length_384(hi_p1);
    int kd_start = ctx->kd_hi[b_hi_cur];
    if (kd_start > b_hi_cur) return;
    u384 span = u1_p1 - l1_p1;
    u384 p3k_g_run = p3_mod384(kd_start) * g_val;

    for (int kd = kd_start; kd <= b_hi_cur; kd++) {
        if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
            ctx->aborted = 1;
            return;
        }
        int s_kkd = k_exp + kd;
        if (s_kkd >= k_coll) {
            u384 rc = ((u384)0 - g_val) * g_inv3_full[w_exp];
            test_congruence_two_vertex(ctx, rc, s_kkd, l1_p1, u1_p1, span);
            return;
        }
        u384 p3k_g = p3k_g_run;
        p3k_g_run += (p3k_g_run << 1);

        u384 u_max = shr384(hi_p1, kd);
        if (u_max == 0) continue;
        if (((u64)u_max & 1ULL) == 0ULL) u_max -= 1;
        if (u_max < 1) continue;
        u384 u_min_l = shr384(lo_p1 + g_mask384[kd], kd);
        if (u_min_l > u_max) continue;

        u640 ev_max = mul_p3_u640(kd, u_max) - (u640)1;
        if (ev_max <= (u640)ctx->two_b_hi) continue;
        u384 inv_wn = g_inv3_full[w_exp + kd];
        u384 sh_kkd = shl384((u384)1, s_kkd);
        u384 base_r = (sh_kkd - p3k_g) * inv_wn;
        int ld_lim = bit_length_640(ev_max) - ctx->b_hi_bl + 2;
        u640 z_ev = ev_max >> 1;
        for (int ld = 1; ld <= ld_lim; ld++, z_ev >>= 1) {
            if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
                ctx->aborted = 1;
                return;
            }
            if (z_ev <= (u640)ctx->b_hi) break;
            int k_n = s_kkd + ld;
            if (k_n >= k_coll) {
                test_congruence_two_vertex(ctx, base_r, k_n, l1_p1, u1_p1, span);
                if (ctx->aborted) return;
                break;
            }
            u384 re = base_r - shl384(inv_wn, k_n);
            test_congruence_two_vertex(ctx, re, k_n + 1, l1_p1, u1_p1, span);
            if (ctx->aborted) return;
        }
    }
}

static void eval_leaf_bridge_two_vertex(
    HenselCtx *ctx,
    int k_exp,
    int w_exp,
    u384 g_val,
    int g_exact,
    u384 lo_z,
    u384 hi_z,
    u384 l1_p1,
    u384 u1_p1,
    int k_coll
) {
    u384 t_lo = ctx->x2_lo;
    u384 t_hi = ctx->x2_hi;
    if (t_lo > t_hi) return;
    u384 hi_p1 = hi_z + 1;
    u384 lo_p1 = lo_z + 1;
    if (!tighten_affine_two_vertex(ctx, k_exp, w_exp, g_val, g_exact, &lo_p1, &hi_p1)) return;
    int b_hi_cur = bit_length_384(hi_p1);
    int kd_start = ctx->kd_lo_bridge[b_hi_cur];
    if (kd_start > b_hi_cur) return;
    u384 span = u1_p1 - l1_p1;
    u384 two_t_lo = 2 * t_lo;
    u384 p3k_g_run = p3_mod384(kd_start) * g_val;

    for (int kd = kd_start; kd <= b_hi_cur; kd++) {
        if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
            ctx->aborted = 1;
            return;
        }
        int s_kkd = k_exp + kd;
        if (s_kkd >= k_coll) {
            u384 rc = ((u384)0 - g_val) * g_inv3_full[w_exp];
            test_congruence_two_vertex(ctx, rc, s_kkd, l1_p1, u1_p1, span);
            return;
        }
        u384 p3k_g = p3k_g_run;
        p3k_g_run += (p3k_g_run << 1);

        u384 u_min = shr384(lo_p1 + g_mask384[kd], kd);
        if (u_min < 1) u_min = 1;
        if (((u64)u_min & 1ULL) == 0ULL) u_min += 1;
        u384 u_max = shr384(hi_p1, kd);
        if (u_max < u_min) continue;
        if (((u64)u_max & 1ULL) == 0ULL) u_max -= 1;
        if (u_min > u_max) continue;

        u640 ev_max = mul_p3_u640(kd, u_max) - (u640)1;
        if (ev_max < (u640)two_t_lo) continue;
        u640 ev_min = mul_p3_u640(kd, u_min) - (u640)1;
        int ld_start = bit_length_640(ev_min) - ctx->x2_hi_bl;
        if (ld_start < 1) ld_start = 1;
        if (shr640_clamp384(ev_min, ld_start) > t_hi) ld_start += 1;
        int ld_end = bit_length_640(ev_max) - ctx->x2_lo_bl + 1;
        if (ld_start > ld_end) continue;

        u384 inv_wn = g_inv3_full[w_exp + kd];
        u384 sh_kkd = shl384((u384)1, s_kkd);
        u384 base_r = (sh_kkd - p3k_g) * inv_wn;
        for (int ld = ld_start; ld <= ld_end; ld++) {
            if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
                ctx->aborted = 1;
                return;
            }
            if ((ev_max >> ld) < (u640)t_lo) break;
            if ((ev_min >> ld) > (u640)t_hi) continue;
            int k_n = s_kkd + ld;
            if (k_n >= k_coll) {
                test_congruence_two_vertex(ctx, base_r, k_n, l1_p1, u1_p1, span);
                if (ctx->aborted) return;
                break;
            }
            u384 re = base_r - shl384(inv_wn, k_n);
            test_congruence_two_vertex(ctx, re, k_n + 1, l1_p1, u1_p1, span);
            if (ctx->aborted) return;
        }
    }
}

static void dfs_two_vertex(
    HenselCtx *ctx,
    int depth,
    int k_exp,
    int w_exp,
    u384 g_val,
    int g_exact,
    u384 lo_z,
    u384 hi_z,
    u384 l1_p1,
    u384 u1_p1,
    int k_coll
) {
    if (ctx->aborted) return;
    ctx->nodes++;
    if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
        ctx->aborted = 1;
        return;
    }
    u384 span = u1_p1 - l1_p1;
    if (k_exp + 1 >= k_coll) {
        u384 r = ((u384)0 - g_val) * g_inv3_full[w_exp];
        test_congruence_two_vertex(ctx, r, k_exp + 1, l1_p1, u1_p1, span);
        return;
    }
    int is_br_mode = (ctx->bridge_to_x2 >= 1 && ctx->bridge_to_x2 <= 3) || (ctx->bridge_to_x2 == 5);
    if (depth == ctx->cur_r) {
        if (is_br_mode) {
            eval_leaf_bridge_two_vertex(ctx, k_exp, w_exp, g_val, g_exact, lo_z, hi_z, l1_p1, u1_p1, k_coll);
        } else {
            eval_leaf_exit_two_vertex(ctx, k_exp, w_exp, g_val, g_exact, lo_z, hi_z, l1_p1, u1_p1, k_coll);
        }
        return;
    }

    u384 hi_p1 = hi_z + 1;
    u384 lo_p1 = lo_z + 1;
    if (!tighten_affine_two_vertex(ctx, k_exp, w_exp, g_val, g_exact, &lo_p1, &hi_p1)) return;
    int b_hi_cur = bit_length_384(hi_p1);
    int kd_start = ctx->kd_lo[b_hi_cur];
    if (kd_start > b_hi_cur) return;
    u384 p3k_g_run = p3_mod384(kd_start) * g_val;

    for (int kd = kd_start; kd <= b_hi_cur; kd++) {
        if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
            ctx->aborted = 1;
            return;
        }
        int s_kkd = k_exp + kd;
        if (s_kkd >= k_coll) {
            u384 rc = ((u384)0 - g_val) * g_inv3_full[w_exp];
            test_congruence_two_vertex(ctx, rc, s_kkd, l1_p1, u1_p1, span);
            return;
        }
        u384 p3k_g = p3k_g_run;
        p3k_g_run += (p3k_g_run << 1);

        u384 u_min = shr384(lo_p1 + g_mask384[kd], kd);
        if (u_min < 1) u_min = 1;
        if (((u64)u_min & 1ULL) == 0ULL) u_min += 1;
        u384 u_max = shr384(hi_p1, kd);
        if (u_max < u_min) continue;
        if (((u64)u_max & 1ULL) == 0ULL) u_max -= 1;
        if (u_min > u_max) continue;

        int w_n = w_exp + kd;
        u640 ev_max = mul_p3_u640(kd, u_max) - (u640)1;
        if (ev_max < (u640)ctx->two_b_lo) continue;
        u640 ev_min = mul_p3_u640(kd, u_min) - (u640)1;
        int ld_start = bit_length_640(ev_min) - ctx->b_hi_bl;
        if (ld_start < 1) ld_start = 1;
        if (shr640_clamp384(ev_min, ld_start) > ctx->b_hi) ld_start += 1;
        int ld_end = bit_length_640(ev_max) - ctx->b_lo_bl + 1;
        if (ld_start > ld_end) continue;

        u384 inv_wn = g_inv3_full[w_n];
        u384 sh_kkd = shl384((u384)1, s_kkd);
        u384 base_r = (sh_kkd - p3k_g) * inv_wn;
        const int *nxt_tbl = (depth + 1 < ctx->cur_r)
            ? ctx->kd_lo
            : (is_br_mode ? ctx->kd_lo_bridge : ctx->kd_hi);

        for (int ld = ld_start; ld <= ld_end; ld++) {
            if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
                ctx->aborted = 1;
                return;
            }
            u384 z_next_max = shr640_clamp384(ev_max, ld);
            if (z_next_max < ctx->b_lo) break;
            u384 z_next_min = shr640_clamp384(ev_min, ld);
            if (z_next_min > ctx->b_hi) continue;
            int k_n = s_kkd + ld;
            if (k_n >= k_coll) {
                test_congruence_two_vertex(ctx, base_r, k_n, l1_p1, u1_p1, span);
                if (ctx->aborted) return;
                break;
            }
            u384 n_hi = (z_next_max >= ctx->b_hi)
                ? ctx->b_hi
                : ((((u64)z_next_max & 1ULL) != 0ULL) ? z_next_max : (z_next_max - 1));
            u384 n_lo = (z_next_min <= ctx->b_lo) ? ctx->b_lo : (z_next_min | (u384)1);
            if (n_lo <= n_hi) {
                int b_nhi_nxt = bit_length_384(n_hi + 1);
                int ks_nxt = nxt_tbl[b_nhi_nxt];
                if (ks_nxt > b_nhi_nxt) continue;
                int s_exp_nxt = k_n + ks_nxt;
                if (s_exp_nxt >= k_coll) {
                    u384 re = base_r - shl384(inv_wn, k_n);
                    test_congruence_two_vertex(ctx, re, s_exp_nxt, l1_p1, u1_p1, span);
                    if (ctx->aborted) return;
                    continue;
                }
                u384 g_n = p3k_g + sh_kkd * g_mask384[ld];
                int g_exact_nxt = (g_exact && (kd * 820 + bit_length_384(g_val) * 512 < 380 * 512)) ? 1 : 0;
                dfs_two_vertex(ctx, depth + 1, k_n, w_n, g_n, g_exact_nxt, n_lo, n_hi, l1_p1, u1_p1, k_coll);
                if (ctx->aborted) return;
            }
        }
    }
}

HENSEL_EXPORT int run_hensel_two_vertex_c(
    const u384_io *n0_io,
    const u384_io *b1_io,
    const u384_io *b2_io,
    const u384_io *x2_lo_io,
    const u384_io *x2_hi_io,
    int max_r,
    int bridge_to_x2,
    int num_bands,
    const BandIO *bands,
    const int *kd_lo,
    const int *kd_hi,
    const int *kd_lo_bridge,
    u64 max_budget,
    u64 *out_nodes,
    u64 *out_leaf_ops,
    int *out_num_survivors,
    u384_io *out_survivors
) {
    ensure_tables();
    if (max_r < 0 || max_r > 15) return -4;
    HenselCtx ctx;
    ctx.n0_threshold = load_u384(n0_io);
    u384 b1_val = load_u384(b1_io);
    u384 b2_val = load_u384(b2_io);
    u384 x2_lo_in = load_u384(x2_lo_io);
    u384 x2_hi_in = load_u384(x2_hi_io);

    ctx.b_hi = b2_val;
    ctx.two_b_hi = 2 * ctx.b_hi;
    ctx.b_hi_bl = bit_length_384(ctx.b_hi);
    ctx.mod_mask = ~(u384)0;
    ctx.loc_mask = ~(u384)0;
    ctx.loc_bits = 384;
    ctx.max_r_verify = max_r;
    ctx.kd_lo = kd_lo;
    ctx.kd_hi = kd_hi;
    ctx.kd_lo_bridge = kd_lo_bridge;
    ctx.is_windowed = 0;
    ctx.is_two_vertex = 1;
    ctx.bridge_to_x2 = (bridge_to_x2 >= 0 && bridge_to_x2 <= 5) ? bridge_to_x2 : (bridge_to_x2 ? 1 : 0);
    ctx.nodes = 0;
    ctx.leaf_ops = 0;
    ctx.max_budget = max_budget;
    ctx.aborted = 0;
    ctx.max_survivors = MAX_SURVIVORS;
    ctx.num_survivors = 0;
    ctx.out_survivors = out_survivors;

    for (int b = 0; b < num_bands; b++) {
        if ((ctx.nodes + ctx.leaf_ops) > ctx.max_budget) {
            ctx.aborted = 1;
            break;
        }
        int k1 = bands[b].k1;
        if (k1 < 1 || k1 >= 360) continue;
        u384 lo1 = load_u384(&bands[b].lo1);
        u384 hi1 = load_u384(&bands[b].hi1);
        if (lo1 > hi1) continue;
        u384 u_min_in = load_u384(&bands[b].u_min);
        u384 u_max_in = load_u384(&bands[b].u_max);
        if (u_min_in > u_max_in) continue;
        if (u_min_in > 0 && bit_length_384(u_min_in) + k1 > 384) continue;

        u384 l1_p1 = lo1 + 1;
        u384 u1_p1 = hi1 + 1;
        u384 l_eff = shl384(u_min_in, k1);
        if (l_eff > l1_p1) l1_p1 = l_eff;
        if (bit_length_384(u_max_in) + k1 <= 384) {
            u384 u_eff = shl384(u_max_in, k1);
            if (u_eff < u1_p1) u1_p1 = u_eff;
        }
        if (l1_p1 > u1_p1) continue;

        u384 u_min = shr384(l1_p1 + g_mask384[k1], k1);
        if (u_min < 1) u_min = 1;
        if (((u64)u_min & 1ULL) == 0ULL) u_min += 1;
        u384 u_max = shr384(u1_p1, k1);
        if (u_max < u_min) continue;
        if (((u64)u_max & 1ULL) == 0ULL) u_max -= 1;
        if (u_min > u_max) continue;

        u384 t_lo;
        u384 eff_blo = (b1_val + 1) | (u384)1;
        if (ctx.bridge_to_x2 == 3 || ctx.bridge_to_x2 == 5) {
            t_lo = x2_lo_in | (u384)1;
        } else {
            t_lo = lo1 + 2;
            if (x2_lo_in > t_lo) t_lo = x2_lo_in;
            t_lo |= (u384)1;
            if (t_lo > eff_blo) eff_blo = t_lo;
        }
        ctx.b_lo = eff_blo;
        ctx.two_b_lo = 2 * eff_blo;
        ctx.b_lo_bl = bit_length_384(eff_blo);

        ctx.l_eff = l1_p1;
        ctx.u_eff = u1_p1;
        ctx.u_eff_bl = bit_length_384(u1_p1);
        u384 span = u1_p1 - l1_p1;
        int k_coll = bit_length_384(span);
        if (k_coll < 1) k_coll = 1;

        u640 ev_min = mul_p3_u640(k1, u_min) - (u640)1;
        u640 ev_max = mul_p3_u640(k1, u_max) - (u640)1;
        if (ctx.bridge_to_x2 == 0 && (ev_max >> 1) > (u640)b2_val) {
            return -3;
        }

        if ((ctx.bridge_to_x2 >= 1 && ctx.bridge_to_x2 <= 3) || ctx.bridge_to_x2 == 5) {
            u384 t_hi = (((u64)x2_hi_in & 1ULL) != 0ULL) ? x2_hi_in : (x2_hi_in > 0 ? x2_hi_in - 1 : 0);
            if (t_lo > t_hi) continue;
            ctx.x2_lo = t_lo;
            ctx.x2_hi = t_hi;
            ctx.x2_lo_bl = bit_length_384(t_lo);
            ctx.x2_hi_bl = bit_length_384(t_hi);

            // Step cur_r = 0: direct 1-step bridge z_1 -> z_2 in [t_lo, t_hi] (when bridge_to_x2 == 1 or 3)
            if ((ctx.bridge_to_x2 == 1 || ctx.bridge_to_x2 == 3) && ev_max >= (u640)(2 * t_lo)) {
                int l1_s = bit_length_640(ev_min) - ctx.x2_hi_bl;
                if (l1_s < 1) l1_s = 1;
                if (shr640_clamp384(ev_min, l1_s) > t_hi) l1_s += 1;
                int l1_e = bit_length_640(ev_max) - ctx.x2_lo_bl + 2;
                if (l1_e < l1_s) l1_e = l1_s;
                u384 sh_k1 = shl384((u384)1, k1);
                u384 inv_k1 = g_inv3_full[k1];
                u384 base_r = sh_k1 * inv_k1;
                ctx.nodes++;
                if ((ctx.nodes + ctx.leaf_ops) > ctx.max_budget) {
                    ctx.aborted = 1;
                    break;
                }
                for (int l1 = l1_s; l1 <= l1_e; l1++) {
                    if ((ctx.nodes + ctx.leaf_ops) > ctx.max_budget) {
                        ctx.aborted = 1;
                        break;
                    }
                    if ((ev_max >> l1) < (u640)t_lo) break;
                    if ((ev_min >> l1) > (u640)t_hi) continue;
                    int k_n = k1 + l1;
                    if (k_n >= k_coll) {
                        test_congruence_two_vertex(&ctx, base_r, k_n, l1_p1, u1_p1, span);
                        break;
                    }
                    u384 re = base_r - shl384(inv_k1, k_n);
                    test_congruence_two_vertex(&ctx, re, k_n + 1, l1_p1, u1_p1, span);
                    if (ctx.aborted) break;
                }
                if (ctx.aborted) break;
            }
        } else {
            ctx.x2_lo = t_lo;
            ctx.x2_hi = b2_val;
            ctx.x2_lo_bl = bit_length_384(t_lo);
            ctx.x2_hi_bl = ctx.b_hi_bl;
            if (ctx.bridge_to_x2 == 4 && ev_max > (u640)ctx.two_b_hi) {
                u384 sh_k1 = shl384((u384)1, k1);
                u384 inv_k1 = g_inv3_full[k1];
                u384 base_r = sh_k1 * inv_k1;
                int ld_lim = bit_length_640(ev_max) - ctx.b_hi_bl + 2;
                ctx.nodes++;
                if ((ctx.nodes + ctx.leaf_ops) > ctx.max_budget) {
                    ctx.aborted = 1;
                    break;
                }
                u640 z_ev = ev_max >> 1;
                for (int l1 = 1; l1 <= ld_lim; l1++, z_ev >>= 1) {
                    if ((ctx.nodes + ctx.leaf_ops) > ctx.max_budget) {
                        ctx.aborted = 1;
                        break;
                    }
                    if (z_ev <= (u640)ctx.b_hi) break;
                    int k_n = k1 + l1;
                    if (k_n >= k_coll) {
                        test_congruence_two_vertex(&ctx, base_r, k_n, l1_p1, u1_p1, span);
                        if (ctx.aborted) break;
                        break;
                    }
                    u384 re = base_r - shl384(inv_k1, k_n);
                    test_congruence_two_vertex(&ctx, re, k_n + 1, l1_p1, u1_p1, span);
                    if (ctx.aborted) break;
                }
                if (ctx.aborted) break;
            }
        }

        if (max_r >= 1 && eff_blo <= b2_val) {
            int ld_start = bit_length_640(ev_min) - ctx.b_hi_bl;
            if (ld_start < 1) ld_start = 1;
            if (shr640_clamp384(ev_min, ld_start) > ctx.b_hi) ld_start += 1;
            int l1_end = bit_length_640(ev_max) - ctx.b_lo_bl + 2;
            if (l1_end < ld_start) l1_end = ld_start;
            for (int cur_r = 1; cur_r <= max_r; cur_r++) {
                ctx.cur_r = cur_r;
                for (int l1 = ld_start; l1 <= l1_end; l1++) {
                    if ((ctx.nodes + ctx.leaf_ops) > ctx.max_budget) {
                        ctx.aborted = 1;
                        break;
                    }
                    u384 z2_max = shr640_clamp384(ev_max, l1);
                    if (z2_max < ctx.b_lo) break;
                    u384 z2_min = shr640_clamp384(ev_min, l1);
                    if (z2_min > ctx.b_hi) continue;
                    u384 z2_min_odd = z2_min | (u384)1;
                    u384 n_lo = (ctx.b_lo >= z2_min_odd) ? ctx.b_lo : z2_min_odd;
                    u384 z2_max_odd = (((u64)z2_max & 1ULL) != 0ULL) ? z2_max : (z2_max - 1);
                    u384 n_hi = (ctx.b_hi <= z2_max_odd) ? ctx.b_hi : z2_max_odd;
                    if (n_lo <= n_hi) {
                        u384 g1 = shl384((u384)1, k1) * (shl384((u384)1, l1) - 1);
                        int g_exact = (k1 + l1 < 384) ? 1 : 0;
                        dfs_two_vertex(&ctx, 1, k1 + l1, k1, g1, g_exact, n_lo, n_hi, l1_p1, u1_p1, k_coll);
                        if (ctx.aborted) break;
                    }
                }
                if (ctx.aborted) break;
            }
        }
        if (ctx.aborted) break;
    }

    if (ctx.aborted == 0 && (ctx.nodes + ctx.leaf_ops) > ctx.max_budget) {
        ctx.aborted = 1;
    }
    *out_nodes = ctx.nodes;
    *out_leaf_ops = ctx.leaf_ops;
    *out_num_survivors = ctx.num_survivors;
    return ctx.aborted;
}

// ============================================================================
// Pure-u128 / u256f Q126 Escalating Window & Pyramid Hensel Frontier Kernels
// ============================================================================

#if defined(_WIN32)
void *memcpy(void *dst, const void *src, __SIZE_TYPE__ n) {
    void *ret = dst;
    __asm__ volatile("rep movsb" : "+D"(dst), "+S"(src), "+c"(n) : : "memory");
    return ret;
}

void *memset(void *dst, int c, __SIZE_TYPE__ n) {
    void *ret = dst;
    __asm__ volatile("rep stosb" : "+D"(dst), "+c"(n) : "a"((unsigned char)c) : "memory");
    return ret;
}

__attribute__((noinline)) static u64 precommit_stack_step_win64(int rem_kb) {
    volatile u64 page_touch[128];
    page_touch[0] = (u64)rem_kb;
    page_touch[127] = (u64)rem_kb ^ 0x5a5a5a5aULL;
    u64 acc = (rem_kb > 1) ? precommit_stack_step_win64(rem_kb - 1) : 0ULL;
    return acc ^ page_touch[0] ^ page_touch[127];
}

static inline void ensure_stack_committed_win64(void) {
    (void)precommit_stack_step_win64(160);
}
#else
static inline void ensure_stack_committed_win64(void) {}
#endif


typedef struct {
    u128 lo;
    u128 hi;
} u256f;

static inline u256f mul128_to_256f(u128 a, u128 b) {
    u64 a0 = (u64)a, a1 = (u64)(a >> 64);
    u64 b0 = (u64)b, b1 = (u64)(b >> 64);
    u128 p00 = (u128)a0 * (u128)b0;
    u128 p01 = (u128)a0 * (u128)b1;
    u128 p10 = (u128)a1 * (u128)b0;
    u128 p11 = (u128)a1 * (u128)b1;
    u128 mid = (p00 >> 64) + (u128)(u64)p01 + (u128)(u64)p10;
    u256f res;
    res.lo = ((u128)(u64)p00) | (mid << 64);
    res.hi = p11 + (p01 >> 64) + (p10 >> 64) + (mid >> 64);
    return res;
}

static inline u256f u256f_mul_u128(u256f g, u128 m) {
    u256f p = mul128_to_256f(g.lo, m);
    if (g.hi) p.hi += g.hi * m;
    return p;
}

static inline u256f u256f_add(u256f a, u256f b) {
    u256f r;
    r.lo = a.lo + b.lo;
    r.hi = a.hi + b.hi + (u128)(r.lo < a.lo);
    return r;
}

static inline u256f u256f_add_u128(u256f a, u128 b) {
    u256f r;
    r.lo = a.lo + b;
    r.hi = a.hi + (u128)(r.lo < a.lo);
    return r;
}

static inline u256f u256f_sub1(u256f a) {
    u256f r;
    r.hi = a.hi - (u128)(a.lo == 0);
    r.lo = a.lo - 1;
    return r;
}

static inline int u256f_gt(u256f a, u256f b) {
    return (a.hi > b.hi) || ((a.hi == b.hi) && (a.lo > b.lo));
}

static inline u256f u256f_sub(u256f a, u256f b) {
    u256f r;
    r.hi = a.hi - b.hi - (u128)(a.lo < b.lo);
    r.lo = a.lo - b.lo;
    return r;
}

static inline u256f u256f_shl_u128(u128 x, int sh) {
    u256f r;
    if (sh <= 0) {
        r.lo = x;
        r.hi = 0;
    } else if (sh < 128) {
        r.lo = x << sh;
        r.hi = x >> (128 - sh);
    } else if (sh < 256) {
        r.lo = 0;
        r.hi = x << (sh - 128);
    } else {
        r.lo = 0;
        r.hi = 0;
    }
    return r;
}

static inline u256f u256f_shr(u256f a, int sh) {
    u256f r;
    if (sh <= 0) return a;
    if (sh < 128) {
        r.lo = (a.lo >> sh) | (a.hi << (128 - sh));
        r.hi = a.hi >> sh;
    } else if (sh < 256) {
        r.lo = a.hi >> (sh - 128);
        r.hi = 0;
    } else {
        r.lo = 0;
        r.hi = 0;
    }
    return r;
}

static inline u256f u256f_shr1(u256f a) {
    u256f r;
    r.lo = (a.lo >> 1) | (a.hi << 127);
    r.hi = a.hi >> 1;
    return r;
}

static inline int bit_length_128(u128 x) {
    u64 hi = (u64)(x >> 64);
    if (hi) return 128 - __builtin_clzll(hi);
    u64 lo = (u64)x;
    return lo ? (64 - __builtin_clzll(lo)) : 0;
}

static inline int bit_length_256f(u256f x) {
    if (x.hi) return 128 + bit_length_128(x.hi);
    return bit_length_128(x.lo);
}

static inline int u256f_lt_u128(u256f a, u128 b) {
    return (a.hi == 0) && (a.lo < b);
}

static inline int u256f_le_u128(u256f a, u128 b) {
    return (a.hi == 0) && (a.lo <= b);
}

static inline int u256f_gt_u128(u256f a, u128 b) {
    return (a.hi != 0) || (a.lo > b);
}

static int g_q126_ready = 0;

static u64 g_inv_z_ub_tbl[130][2048];
static u64 g_inv_zp1_lb_tbl[130][2048];
static u64 g_num23_ub_q62[256];
static u64 g_num23_lb_q62[256];
static u256 g_p3_256[160];
static u128 g_p3_128[81];
static u128 g_max_u_128[81];
static int g_p3_bl[195];
static u128 g_recip3_lb[195];
static u128 g_recip3_ub[195];
static int g_kd_jump[140];

static inline int bit_length_256(u256 x) {
    u128 hi = (u128)(x >> 128);
    if (hi) return 128 + bit_length_128(hi);
    return bit_length_128((u128)x);
}

static inline int min_kd_for_jump(int b_cur, int b_tgt) {
    int diff = b_tgt - b_cur;
    if (diff <= 0) return 1;
    if (diff >= 140) return 240;
    return g_kd_jump[diff];
}

static inline u128 div3_u128(u128 x) {
    u64 hi = (u64)(x >> 64);
    u64 lo = (u64)x;
    u64 q_hi = hi / 3ULL;
    u64 r = hi % 3ULL;
    u64 m1 = (r << 32) | (lo >> 32);
    u64 q_m1 = m1 / 3ULL;
    r = m1 % 3ULL;
    u64 m0 = (r << 32) | (lo & 0xFFFFFFFFULL);
    u64 q_m0 = m0 / 3ULL;
    return (((u128)q_hi) << 64) | (((u128)q_m1) << 32) | (u128)q_m0;
}

/* Exact floor(2^sh / d) and remainder using single 64-bit hardware divq when 2^(sh-64) < d. */
static inline u128 div_pow2_u64_u128_floor(int sh, u64 d, u64 *rem_out) {
    if (sh < 0) {
        *rem_out = 1ULL;
        return (u128)0;
    }
    if (sh <= 62) {
        u64 num = 1ULL << sh;
        *rem_out = num % d;
        return (u128)(num / d);
    }
    if (sh <= 126) {
        u64 hi = (sh >= 64) ? (1ULL << (sh - 64)) : 0ULL;
        if (hi < d) {
            u64 q_hw = 0ULL;
            u64 r_hw = hi;
            u64 lo_hw = (sh == 63) ? (1ULL << 63) : 0ULL;
            __asm__(
                "divq %[div]"
                : "=a"(q_hw), "=d"(r_hw)
                : "d"(r_hw), "a"(lo_hw), [div] "r"(d)
                : "cc"
            );
            *rem_out = r_hw;
            return (u128)q_hw;
        }
    }
    int cur = sh - 54;
    u64 r = 1ULL << 54;
    u128 q_acc = (u128)(r / d);
    r = r % d;
    while (cur > 0) {
        int step = (cur > 9) ? 9 : cur;
        r <<= step;
        u64 dq = r / d;
        r = r % d;
        q_acc = (q_acc << step) + (u128)dq;
        cur -= step;
    }
    *rem_out = r;
    return q_acc;
}

static void ensure_q126_tables(void) {
    if (g_q126_ready) return;
    ensure_tables();
    for (int b = 12; b < 130; b++) {
        int s = b - 11;
        int sh = 126 - s;
        for (int top = 1024; top < 2048; top++) {
            u64 rem_ub = 0ULL, rem_lb = 0ULL;
            u128 q_ub = div_pow2_u64_u128_floor(sh, (u64)top, &rem_ub);
            if (rem_ub != 0ULL) q_ub += 1;
            u64 v_ub = (q_ub >= (u128)0x00FFFFFFFFFFFFFFULL) ? 0x00FFFFFFFFFFFFFFULL : (u64)q_ub;
            g_inv_z_ub_tbl[b][top] = v_ub;

            u128 q_lb = div_pow2_u64_u128_floor(sh, (u64)(top + 1), &rem_lb);
            u64 v_lb = (q_lb > (u128)0x00FFFFFFFFFFFFFFULL) ? 0x00FFFFFFFFFFFFFFULL : (u64)q_lb;
            g_inv_zp1_lb_tbl[b][top] = v_lb;
        }
    }
    u128 rk_lo = ((u128)1) << 96;
    u128 rk_hi = ((u128)1) << 96;
    g_num23_ub_q62[0] = 0;
    g_num23_lb_q62[0] = 0;
    for (int k = 1; k < 256; k++) {
        rk_lo = div3_u128(rk_lo << 1);
        rk_hi = div3_u128((rk_hi << 1) + 2);
        u64 lb_q62 = (u64)(rk_lo >> 34);
        u64 ub_q62 = (u64)((rk_hi + (((u128)1 << 34) - 1)) >> 34);
        g_num23_ub_q62[k] = (1ULL << 62) - lb_q62;
        u64 raw_lb62 = (ub_q62 < (1ULL << 62)) ? ((1ULL << 62) - ub_q62) : 0ULL;
        g_num23_lb_q62[k] = (raw_lb62 > 64ULL) ? (raw_lb62 - 64ULL) : 0ULL;
    }
    for (int k = 0; k < 160; k++) {
        g_p3_256[k] = (u256)g_p3[k];
    }
    g_p3_128[0] = (u128)1;
    g_max_u_128[0] = ~(u128)0;
    g_p3_bl[0] = 1;
    g_recip3_lb[0] = ((u128)1) << 127;
    g_recip3_ub[0] = ((u128)1) << 127;
    for (int k = 1; k <= 80; k++) {
        u128 p3w = g_p3_128[k - 1] * (u128)3;
        g_p3_128[k] = p3w;
        g_max_u_128[k] = div3_u128(g_max_u_128[k - 1]);
        int bw = bit_length_128(p3w);
        g_p3_bl[k] = bw;
        u128 rem = (u128)1;
        u128 quo = (u128)0;
        int n_sh = 126 + bw;
        for (int st = 0; st < n_sh; st++) {
            rem <<= 1;
            quo <<= 1;
            if (rem >= p3w) {
                rem -= p3w;
                quo |= (u128)1;
            }
        }
        g_recip3_lb[k] = quo;
        g_recip3_ub[k] = quo + (u128)1;
    }
    for (int k = 81; k <= 190; k++) {
        u384 p3w = g_p3[k];
        int bw = bit_length_fast(p3w);
        g_p3_bl[k] = bw;
        u384 rem = (u384)1;
        u128 quo = (u128)0;
        int n_sh = 126 + bw;
        for (int st = 0; st < n_sh; st++) {
            rem <<= 1;
            quo <<= 1;
            if (rem >= p3w) {
                rem -= p3w;
                quo |= (u128)1;
            }
        }
        g_recip3_lb[k] = quo;
        g_recip3_ub[k] = quo + (u128)1;
    }
    g_kd_jump[0] = 1;
    for (int diff = 1; diff < 140; diff++) {
        int kk = 1;
        while (kk < 240 && (diff + kk) < 380 && g_p3[kk] <= (((u384)1) << (diff + kk))) {
            kk++;
        }
        g_kd_jump[diff] = kk;
    }
    g_q126_ready = 1;
}

static inline u64 inv_ub_pow2_126_u384(u384 val) {
    if (val == 0) return 0x00FFFFFFFFFFFFFFULL;
    int bl = bit_length_fast(val);
    if (bl >= 126) return 1ULL;
    int s = (bl > 54) ? (bl - 54) : 0;
    u64 d_lo = (u64)shr384(val, s);
    if (d_lo == 0ULL) d_lo = 1ULL;
    u64 rem = 0ULL;
    u128 q = div_pow2_u64_u128_floor(126 - s, d_lo, &rem);
    if (rem != 0ULL) q += 1;
    return (q >= (u128)0x00FFFFFFFFFFFFFFULL) ? 0x00FFFFFFFFFFFFFFULL : (u64)q;
}

static inline u64 inv_lb_pow2_126_u384(u384 val) {
    int bl = bit_length_fast(val);
    if (bl >= 126) return 0ULL;
    int s = (bl > 54) ? (bl - 54) : 0;
    u64 d_hi = (u64)shr384(val, s) + ((s > 0) ? 1ULL : 0ULL);
    u64 rem = 0ULL;
    u128 q = div_pow2_u64_u128_floor(126 - s, d_hi, &rem);
    return (q > (u128)0x00FFFFFFFFFFFFFFULL) ? 0x00FFFFFFFFFFFFFFULL : (u64)q;
}

/* 54-bit exact versions (called ONCE per root band at depth = 0). */
static inline u64 inv_z_ub_exact_q126(u384 z_min) {
    return inv_ub_pow2_126_u384(z_min);
}

static inline u64 inv_zp1_lb_exact_q126(u384 z_max) {
    return inv_lb_pow2_126_u384(z_max + 1);
}

/* Fast O(1) 11-bit L1-table versions (called inside DFS for depth >= 1, zero divq!). */
static inline u64 inv_z_ub_fast_q126(u384 z_min) {
    int b = bit_length_fast(z_min);
    if (b >= 126) return 1ULL;
    if (b < 12) return 0x00FFFFFFFFFFFFFFULL;
    u64 top = (u64)shr384(z_min, b - 11);
    return g_inv_z_ub_tbl[b][top];
}

static inline u64 inv_zp1_lb_fast_q126(u384 z_max) {
    u384 zp1 = z_max + 1;
    int b = bit_length_fast(zp1);
    if (b >= 126) return 0ULL;
    if (b < 12) return inv_lb_pow2_126_u384(zp1);
    u64 top = (u64)shr384(zp1, b - 11);
    return g_inv_zp1_lb_tbl[b][top];
}

static inline u64 step_term_ub_exact_q126(u384 z_min, int kd) {
    u64 inv_z = inv_z_ub_exact_q126(z_min);
    u64 mult = (kd < 256) ? g_num23_ub_q62[kd] : (1ULL << 62);
    return (u64)((((u128)inv_z * (u128)mult) + ((1ULL << 62) - 1ULL)) >> 62);
}

static inline u64 step_term_ub_fast_q126(u384 z_min, int kd) {
    u64 inv_z = inv_z_ub_fast_q126(z_min);
    u64 mult = (kd < 256) ? g_num23_ub_q62[kd] : (1ULL << 62);
    return (u64)((((u128)inv_z * (u128)mult) + ((1ULL << 62) - 1ULL)) >> 62);
}

static inline u64 step_term_lb_exact_q126(u384 z_max, int kd) {
    u64 inv_z = inv_zp1_lb_exact_q126(z_max);
    u64 mult = (kd < 256) ? g_num23_lb_q62[kd] : g_num23_lb_q62[255];
    return (u64)(((u128)inv_z * (u128)mult) >> 62);
}

static inline u64 step_term_lb_fast_q126(u384 z_max, int kd) {
    u64 inv_z = inv_zp1_lb_fast_q126(z_max);
    u64 mult = (kd < 256) ? g_num23_lb_q62[kd] : g_num23_lb_q62[255];
    return (u64)(((u128)inv_z * (u128)mult) >> 62);
}

static inline int ctz_128_fast(u128 x) {
    u64 lo = (u64)x;
    if (lo) return __builtin_ctzll(lo);
    return 64 + __builtin_ctzll((u64)(x >> 64));
}

static inline int ctz_256_fast(u256 x) {
    u128 lo = (u128)x;
    if (lo) return ctz_128_fast(lo);
    return 128 + ctz_128_fast((u128)(x >> 128));
}

/* Pure u128/u256f next odd spiral minimum when cur < 2^124: returns 1 if next > b_hi_128, else 0 and writes *out_nxt. */
static inline int next_spiral_u128_check(u128 cur, u128 b_hi_128, u128 *out_nxt) {
    u128 xp1 = cur + 1;
    int k = ctz_128_fast(xp1);
    u128 u = xp1 >> k;
    if (__builtin_expect(k <= 80 && u <= g_max_u_128[k], 1)) {
        u128 ev128 = g_p3_128[k] * u - 1;
        int l = ctz_128_fast(ev128);
        u128 nxt128 = ev128 >> l;
        if (nxt128 > b_hi_128) return 1;
        *out_nxt = nxt128;
        return 0;
    }
    if (__builtin_expect(k <= 80, 1)) {
        u256f evf = u256f_sub1(mul128_to_256f(g_p3_128[k], u));
        int l = (evf.lo != 0) ? ctz_128_fast(evf.lo) : (128 + ctz_128_fast(evf.hi));
        u256f nxtf = u256f_shr(evf, l);
        if (u256f_gt_u128(nxtf, b_hi_128)) return 1;
        *out_nxt = nxtf.lo;
        return 0;
    }
    u256 ev = g_p3_256[k] * (u256)u - 1;
    int l = ctz_256_fast(ev);
    u256 nxt = ev >> l;
    if (nxt > (u256)b_hi_128) return 1;
    *out_nxt = (u128)nxt;
    return 0;
}

static inline void verify_z1_std_u128(HenselCtx *ctx, u128 z) {
    if (ctx->aborted) return;
    if (((u64)z & 1ULL) == 0ULL || z <= (u128)ctx->n0_threshold) return;
    u128 b_lo_128 = (u128)ctx->b_lo;
    u128 b_hi_128 = (u128)ctx->b_hi;
    u128 cur = z;
    for (int step = 0; step <= ctx->max_r_verify; step++) {
        u128 nxt = 0;
        if (next_spiral_u128_check(cur, b_hi_128, &nxt)) {
            if (step >= 1) add_survivor(ctx, (u384)z);
            return;
        }
        if (nxt < b_lo_128) return;
        cur = nxt;
    }
}

static inline u64 inv_zp1_lb_u128(u128 z_max) {
    u128 zp1 = z_max + 1;
    int b = bit_length_128(zp1);
    if (b >= 126) return 0ULL;
    if (b < 12) return inv_lb_pow2_126_u384((u384)zp1);
    u64 top = (u64)(zp1 >> (b - 11));
    return g_inv_zp1_lb_tbl[b][top];
}


static inline u64 step_term_lb_u128(u128 z_max, int kd) {
    u64 inv_z = inv_zp1_lb_u128(z_max);
    u64 mult = (kd < 256) ? g_num23_lb_q62[kd] : g_num23_lb_q62[255];
    return (u64)(((u128)inv_z * (u128)mult) >> 62);
}

static inline u128 pole_min_next_u128(u64 rem_ulam_q126) {
    if (rem_ulam_q126 == 0ULL) return (((u128)1) << 127) | (u128)1;
    if (rem_ulam_q126 >= (1ULL << 56)) return 1;
    u64 d3 = 3ULL * rem_ulam_q126;
    int bl = 64 - __builtin_clzll(d3);
    int s = (bl > 30) ? (bl - 30) : 0;
    u64 d_hi = (d3 >> s) + ((s > 0) ? 1ULL : 0ULL);
    int sh = 126 - s;
    u128 min_vp1 = (sh <= 62)
        ? (u128)((1ULL << sh) / d_hi)
        : (((u128)((1ULL << 62) / d_hi)) << (sh - 62));
    if (min_vp1 <= 2) return 1;
    return (min_vp1 - 1) | (u128)1;
}

static inline u128 pole_max_cur_u128(u64 req_deficit_q126) {
    if (req_deficit_q126 == 0ULL) return (((u128)1) << 127);
    if (req_deficit_q126 >= (1ULL << 62)) return (u128)(1ULL << 63);
    int bl = 64 - __builtin_clzll(req_deficit_q126);
    int s = (bl > 30) ? (bl - 30) : 0;
    u64 d_lo = req_deficit_q126 >> s;
    int sh = 126 - s;
    u128 q = (u128)((1ULL << 62) / d_lo) + (u128)1;
    return q << (sh - 62);
}

static inline void test_cong_std_u128(
    HenselCtx *ctx,
    u128 diff128,
    int m_exp,
    u128 l1_128,
    u128 u1_128,
    u128 span128
) {
    ctx->leaf_ops++;
    if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
        ctx->aborted = 1;
        return;
    }
    int m_cap = (m_exp > 126) ? 126 : m_exp;
    u128 mm1 = g_mask128[m_cap];
    u128 rem = diff128 & mm1;
    if (rem <= span128) {
        if (m_cap >= 1 && ((((u64)l1_128 + (u64)rem) & 1ULL) != 0ULL)) return;
        u128 step = mm1 + 1;
        u128 f = l1_128 + rem;
        while (f <= u1_128) {
            if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
                ctx->aborted = 1;
                return;
            }
            verify_z1_std_u128(ctx, f - 1);
            ctx->leaf_ops++;
            if (ctx->aborted) return;
            f += step;
        }
    }
}

/* Pure-u128/u256 Standard Hensel DFS (for b2_val < 2^125, u1_p1 < 2^120, k_coll <= 120) */
static void dfs_std_u128(
    HenselCtx *ctx,
    int depth,
    int k_exp,
    int w_exp,
    u256 g256,
    int g_exact,
    u128 lo_z,
    u128 hi_z,
    u64 rem_ulam,
    u128 l1_128,
    u128 u1_128,
    u128 span128,
    int k_coll
) {
    if (ctx->aborted) return;
    ctx->nodes++;
    if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
        ctx->aborted = 1;
        return;
    }
    if (k_exp + 1 >= k_coll) {
        u128 r128 = ((u128)0 - (u128)g256) * (u128)g_inv3[w_exp];
        test_cong_std_u128(ctx, r128 - l1_128, k_exp + 1, l1_128, u1_128, span128);
        return;
    }

    u128 hi_p1 = hi_z + 1;
    u128 lo_p1 = lo_z + 1;
    if (g_exact && w_exp <= 104 && ctx->u_eff_bl <= 86 && ((g256 >> 250) == 0)) {
        u256 p3w = g_p3_256[w_exp];
        u256 z_aff_hi = (p3w * (u256)u1_128 + g256) >> k_exp;
        if (z_aff_hi < (u256)lo_p1) return;
        if (z_aff_hi < (u256)hi_p1) {
            u128 zh = (u128)z_aff_hi;
            if (((u64)zh & 1ULL) != 0ULL) zh -= 1;
            if (zh < lo_p1) return;
            hi_p1 = zh;
        }
        u256 m256 = (((u256)1) << k_exp) - 1;
        u256 z_aff_lo = (p3w * (u256)l1_128 + g256 + m256) >> k_exp;
        if (z_aff_lo > (u256)hi_p1) return;
        if (z_aff_lo > (u256)lo_p1) {
            u128 zl = (u128)z_aff_lo;
            if (((u64)zl & 1ULL) != 0ULL) zl += 1;
            if (zl > hi_p1) return;
            lo_p1 = zl;
        }
    }

    u128 cur_hi = (((u64)(hi_p1 - 1) & 1ULL) != 0ULL) ? (hi_p1 - 1) : (hi_p1 - 2);
    if (rem_ulam != ~0ULL && step_term_lb_u128(cur_hi, 1) >= rem_ulam) return;

    int b_hi_cur = bit_length_128(hi_p1);
    u128 b_lo_128 = (u128)ctx->b_lo;
    u128 b_hi_128 = (u128)ctx->b_hi;

    if (depth == ctx->cur_r) {
        int kd_start = ctx->kd_hi[b_hi_cur];
        if (kd_start > b_hi_cur) return;
        u128 p3k_g128 = (u128)g_p3_256[kd_start] * (u128)g256;
        u256 two_b_hi_256 = (u256)ctx->two_b_hi;
        for (int kd = kd_start; kd <= b_hi_cur; kd++) {
            if (rem_ulam != ~0ULL && step_term_lb_u128(cur_hi, kd) >= rem_ulam) break;
            int s_kkd = k_exp + kd;
            if (s_kkd >= k_coll) {
                u128 rc = ((u128)0 - (u128)g256) * (u128)g_inv3[w_exp];
                test_cong_std_u128(ctx, rc - l1_128, s_kkd, l1_128, u1_128, span128);
                return;
            }
            u128 cur_p3g = p3k_g128;
            p3k_g128 += (p3k_g128 << 1);
            u128 u_max = hi_p1 >> kd;
            if (u_max == 0) continue;
            if (((u64)u_max & 1ULL) == 0ULL) u_max -= 1;
            if (u_max < 1) continue;
            u128 u_min_l = (lo_p1 + g_mask128[kd]) >> kd;
            if (u_min_l > u_max) continue;
            u256 ev_max = g_p3_256[kd] * (u256)u_max - 1;
            if (ev_max <= two_b_hi_256) continue;
            u128 inv_wn = (u128)g_inv3[w_exp + kd];
            u128 bd128 = (((((u128)1) << s_kkd) - cur_p3g) * inv_wn) - l1_128;
            u128 inv_sh = inv_wn << (s_kkd + 1);
            int ld_lim = bit_length_256(ev_max) - ctx->b_hi_bl + 2;
            u256 z_ev = ev_max >> 1;
            for (int ld = 1; ld <= ld_lim; ld++, z_ev >>= 1) {
                if (z_ev <= (u256)b_hi_128) break;
                int k_n = s_kkd + ld;
                if (k_n >= k_coll) {
                    test_cong_std_u128(ctx, bd128, k_n, l1_128, u1_128, span128);
                    break;
                }
                test_cong_std_u128(ctx, bd128 - inv_sh, k_n + 1, l1_128, u1_128, span128);
                inv_sh <<= 1;
            }
        }
        return;
    }

    int next_is_leaf = (depth + 1 == ctx->cur_r);
    int kd_start = ctx->kd_lo[b_hi_cur];
    if (kd_start > b_hi_cur) return;
    u256 p3k_g_run = g_p3_256[kd_start] * g256;

    for (int kd = kd_start; kd <= b_hi_cur; kd++) {
        if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
            ctx->aborted = 1;
            return;
        }
        u64 nxt_rem = rem_ulam;
        if (rem_ulam != ~0ULL) {
            u64 cur_lb = step_term_lb_u128(cur_hi, kd);
            if (cur_lb >= rem_ulam) break;
            nxt_rem = rem_ulam - cur_lb;
        }
        int s_kkd = k_exp + kd;
        if (s_kkd >= k_coll) {
            u128 rc = ((u128)0 - (u128)g256) * (u128)g_inv3[w_exp];
            test_cong_std_u128(ctx, rc - l1_128, s_kkd, l1_128, u1_128, span128);
            break;
        }
        u128 eff_b_lo = b_lo_128;
        if (rem_ulam != ~0ULL) {
            u128 p_nxt = pole_min_next_u128(nxt_rem);
            if (p_nxt > b_hi_128) {
                p3k_g_run += (p3k_g_run << 1);
                continue;
            }
            if (p_nxt > eff_b_lo) eff_b_lo = p_nxt;
        }
        u256 p3k_g = p3k_g_run;
        p3k_g_run += (p3k_g_run << 1);

        u128 u_min = (lo_p1 + g_mask128[kd]) >> kd;
        if (u_min < 1) u_min = 1;
        if (((u64)u_min & 1ULL) == 0ULL) u_min += 1;
        u128 u_max = hi_p1 >> kd;
        if (u_max < u_min) continue;
        if (((u64)u_max & 1ULL) == 0ULL) u_max -= 1;
        if (u_min > u_max) continue;

        u256 ev_max = g_p3_256[kd] * (u256)u_max - 1;
        if (ev_max < (u256)(eff_b_lo << 1)) continue;
        u256 ev_min = g_p3_256[kd] * (u256)u_min - 1;
        int ld_start = bit_length_256(ev_min) - ctx->b_hi_bl;
        if (ld_start < 1) ld_start = 1;
        if ((ev_min >> ld_start) > (u256)b_hi_128) ld_start += 1;
        int ld_end = bit_length_256(ev_max) - bit_length_128(eff_b_lo) + 1;
        if (ld_start > ld_end) continue;
        u256 z_mx = ev_max >> ld_start;
        if (z_mx < (u256)eff_b_lo) continue;

        int w_n = w_exp + kd;
        u128 inv_wn = (u128)g_inv3[w_n];
        u128 sh_kkd_128 = ((u128)1) << s_kkd;
        u128 base_diff_128 = ((sh_kkd_128 - (u128)p3k_g) * inv_wn) - l1_128;

        if (next_is_leaf) {
            u128 inv_sh_128 = inv_wn << (s_kkd + ld_start);
            for (int ld = ld_start; ld <= ld_end; ld++, z_mx >>= 1) {
                if (z_mx < (u256)eff_b_lo) break;
                int k_n = s_kkd + ld;
                if (k_n >= k_coll) {
                    test_cong_std_u128(ctx, base_diff_128, k_n, l1_128, u1_128, span128);
                    break;
                }
                u128 cur_inv = inv_sh_128;
                inv_sh_128 <<= 1;
                int b_nhi = (z_mx >= (u256)b_hi_128) ? ctx->b_hi_bl : bit_length_128((u128)z_mx + 1);
                int ks = ctx->kd_hi[b_nhi];
                if (ks > b_nhi) continue;
                int s_exp = k_n + ks;
                if (s_exp >= k_coll) {
                    test_cong_std_u128(ctx, base_diff_128 - cur_inv, s_exp, l1_128, u1_128, span128);
                } else {
                    u128 n_hi = (z_mx >= (u256)b_hi_128)
                        ? b_hi_128
                        : ((((u64)z_mx & 1ULL) != 0ULL) ? (u128)z_mx : ((u128)z_mx - 1));
                    int g_ex_n = g_exact && ((kd * 2 + bit_length_256(g256)) < 250);
                    u256 g_n = p3k_g + ((u256)sh_kkd_128) * ((((u256)1) << ld) - 1);
                    dfs_std_u128(ctx, depth + 1, k_n, w_n, g_n, g_ex_n, eff_b_lo, n_hi, nxt_rem, l1_128, u1_128, span128, k_coll);
                    if (ctx->aborted) return;
                }
            }
        } else {
            u256 z_mn = ev_min >> ld_start;
            for (int ld = ld_start; ld <= ld_end; ld++, z_mx >>= 1, z_mn >>= 1) {
                if (z_mx < (u256)eff_b_lo) break;
                if (z_mn > (u256)b_hi_128) continue;
                int k_n = s_kkd + ld;
                if (k_n >= k_coll) {
                    test_cong_std_u128(ctx, base_diff_128, k_n, l1_128, u1_128, span128);
                    break;
                }
                u128 n_hi = (z_mx >= (u256)b_hi_128)
                    ? b_hi_128
                    : ((((u64)z_mx & 1ULL) != 0ULL) ? (u128)z_mx : ((u128)z_mx - 1));
                u128 n_lo = (z_mn <= (u256)eff_b_lo) ? eff_b_lo : (((u128)z_mn) | (u128)1);
                if (n_lo <= n_hi) {
                    int b_nhi_nxt = bit_length_128(n_hi + 1);
                    int ks_nxt = ctx->kd_lo[b_nhi_nxt];
                    if (ks_nxt > b_nhi_nxt) continue;
                    int s_exp_nxt = k_n + ks_nxt;
                    if (s_exp_nxt >= k_coll) {
                        test_cong_std_u128(ctx, base_diff_128 - (inv_wn << k_n), s_exp_nxt, l1_128, u1_128, span128);
                    } else {
                        int g_ex_n = g_exact && ((kd * 2 + bit_length_256(g256)) < 250);
                        u256 g_n = p3k_g + ((u256)sh_kkd_128) * ((((u256)1) << ld) - 1);
                        dfs_std_u128(ctx, depth + 1, k_n, w_n, g_n, g_ex_n, n_lo, n_hi, nxt_rem, l1_128, u1_128, span128, k_coll);
                        if (ctx->aborted) return;
                    }
                }
            }
        }
    }
}

__attribute__((noinline)) static int run_hensel_standard_u128_ex_impl(
    const u384_io *n0_io,
    const u384_io *b1_io,
    const u384_io *b2_io,
    int max_r,
    int include_r0,
    int max_survivors_cap,
    u64 ulam_q126,
    int num_bands,
    const BandIO *bands,
    const int *kd_lo,
    const int *kd_hi,
    u64 max_budget,
    u64 *out_nodes,
    u64 *out_leaf_ops,
    int *out_num_survivors,
    u384_io *out_survivors
) {
    ensure_q126_tables();
    u384 n0_v = load_u384(n0_io);
    u384 b1_v = load_u384(b1_io);
    u384 b2_v = load_u384(b2_io);
    int min_r_allowed = include_r0 ? 0 : 1;
    if (bit_length_fast(b2_v) > 126 || max_r < min_r_allowed || max_r > 10) {
        if (include_r0) return -6;
        return run_hensel_standard_c(
            n0_io, b1_io, b2_io, max_r, num_bands, bands, kd_lo, kd_hi,
            max_budget, out_nodes, out_leaf_ops, out_num_survivors, out_survivors
        );
    }
    HenselCtx ctx;
    ctx.n0_threshold = n0_v;
    ctx.b_lo = b1_v + 1;
    ctx.b_hi = b2_v;
    ctx.two_b_lo = 2 * ctx.b_lo;
    ctx.two_b_hi = 2 * ctx.b_hi;
    ctx.b_lo_bl = bit_length_fast(ctx.b_lo);
    ctx.b_hi_bl = bit_length_fast(ctx.b_hi);
    ctx.mod_mask = ~(u384)0;
    ctx.loc_mask = ~(u384)0;
    ctx.loc_bits = 384;
    ctx.max_r_verify = max_r;
    ctx.kd_lo = kd_lo;
    ctx.kd_hi = kd_hi;
    ctx.is_windowed = 0;
    ctx.is_two_vertex = 0;
    ctx.bridge_to_x2 = 0;
    ctx.nodes = 0;
    ctx.leaf_ops = 0;
    ctx.max_budget = max_budget;
    ctx.aborted = 0;
    ctx.max_survivors = (max_survivors_cap > 0) ? max_survivors_cap : MAX_SURVIVORS;
    ctx.num_survivors = 0;
    ctx.out_survivors = out_survivors;

    u128 b_lo_128 = (u128)ctx.b_lo;
    u128 b_hi_128 = (u128)ctx.b_hi;
    u256 two_b_hi_256 = (u256)ctx.two_b_hi;

    for (int b = 0; b < num_bands; b++) {
        if ((ctx.nodes + ctx.leaf_ops) > ctx.max_budget) {
            ctx.aborted = 1;
            break;
        }
        int k1 = bands[b].k1;
        if (k1 < 1 || k1 >= 120) continue;
        u384 lo1 = load_u384(&bands[b].lo1);
        u384 hi1 = load_u384(&bands[b].hi1);
        u384 u_min = load_u384(&bands[b].u_min);
        u384 u_max = load_u384(&bands[b].u_max);
        if (lo1 > hi1 || u_min > u_max) continue;
        u384 l1_p1 = lo1 + 1;
        u384 u1_p1 = hi1 + 1;
        u384 l_eff = shl384(u_min, k1);
        if (l_eff > l1_p1) l1_p1 = l_eff;
        u384 u_eff = shl384(u_max, k1);
        if (u_eff < u1_p1) u1_p1 = u_eff;
        if (l1_p1 > u1_p1) continue;
        if (bit_length_fast(u1_p1) > 120) return -5;

        u128 l1_128 = (u128)l1_p1;
        u128 u1_128 = (u128)u1_p1;
        u128 span128 = u1_128 - l1_128;
        int k_coll = bit_length_128(span128);
        if (k_coll < 1) k_coll = 1;
        int k_stop_std = k_coll;
        ctx.l_eff = l1_p1;
        ctx.u_eff = u1_p1;
        ctx.u_eff_bl = bit_length_128(u1_128);

        u128 u_min_eff = (l1_128 + g_mask128[k1]) >> k1;
        if (((u64)u_min_eff & 1ULL) == 0ULL) u_min_eff += 1;
        u128 u_max_eff = u1_128 >> k1;
        if (u_max_eff < u_min_eff) continue;
        if (((u64)u_max_eff & 1ULL) == 0ULL) u_max_eff -= 1;
        if (u_min_eff > u_max_eff) continue;

        u256 p3_k1 = g_p3_256[k1];
        u64 rem_ulam_1 = ~0ULL;
        if (ulam_q126 > 0ULL) {
            u64 root_lb = step_term_lb_exact_q126((u384)(u1_128 - 1), k1);
            if (root_lb >= ulam_q126) continue;
            rem_ulam_1 = ulam_q126 - root_lb;
        }
        u256 ev_min = p3_k1 * (u256)u_min_eff - 1;
        u256 ev_max = p3_k1 * (u256)u_max_eff - 1;
        if ((ev_max >> 1) > (u256)b_hi_128) {
            if (!include_r0) return -3;
            u256 u_r0_256 = (two_b_hi_256 + p3_k1 + 1) / p3_k1;
            u128 u_r0 = (u_r0_256 > (u256)u_min_eff) ? (u128)u_r0_256 : u_min_eff;
            u_r0 |= (u128)1;
            for (u128 uc = u_r0; uc <= u_max_eff; uc += 2) {
                ctx.leaf_ops++;
                if ((ctx.nodes + ctx.leaf_ops) > ctx.max_budget) {
                    ctx.aborted = 1;
                    break;
                }
                u128 z1_128 = (uc << k1) - 1;
                if (z1_128 > (u128)n0_v) {
                    u128 dummy_nxt = 0;
                    if (next_spiral_u128_check(z1_128, b_hi_128, &dummy_nxt)) {
                        add_survivor(&ctx, (u384)z1_128);
                        if (ctx.aborted) break;
                    }
                }
            }
            if (ctx.aborted) break;
        }
        u128 root_blo = b_lo_128;
        if (rem_ulam_1 != ~0ULL) {
            u128 p1 = pole_min_next_u128(rem_ulam_1);
            if (p1 > b_hi_128) continue;
            if (p1 > root_blo) root_blo = p1;
        }
        if (max_r == 0 || ev_max < (u256)(root_blo << 1)) continue;

        int ld_s = bit_length_256(ev_min) - ctx.b_hi_bl;
        if (ld_s < 1) ld_s = 1;
        if ((ev_min >> ld_s) > (u256)b_hi_128) ld_s += 1;
        int ld_e = bit_length_256(ev_max) - bit_length_128(root_blo) + 2;
        if (ld_e < ld_s) ld_e = ld_s;

        for (int cur_r = 1; cur_r <= max_r; cur_r++) {
            ctx.cur_r = cur_r;
            for (int l1 = ld_s; l1 <= ld_e; l1++) {
                u256 z2_mx = ev_max >> l1;
                if (z2_mx < (u256)root_blo) break;
                u256 z2_mn = ev_min >> l1;
                if (z2_mn > (u256)b_hi_128) continue;
                u128 n_lo = (z2_mn <= (u256)root_blo) ? root_blo : (((u128)z2_mn) | (u128)1);
                u128 n_hi = (z2_mx >= (u256)b_hi_128)
                    ? b_hi_128
                    : ((((u64)z2_mx & 1ULL) != 0ULL) ? (u128)z2_mx : ((u128)z2_mx - 1));
                if (n_lo <= n_hi) {
                    u256 g1 = (((u256)1) << k1) * ((((u256)1) << l1) - 1);
                    int g_ex = (k1 + l1 < 245) ? 1 : 0;
                    dfs_std_u128(&ctx, 1, k1 + l1, k1, g1, g_ex, n_lo, n_hi, rem_ulam_1, l1_128, u1_128, span128, k_stop_std);
                    if (ctx.aborted) break;
                }
            }
            if (ctx.aborted) break;
        }
        if (ctx.aborted) break;
    }
    if (ctx.aborted == 0 && (ctx.nodes + ctx.leaf_ops) > ctx.max_budget) ctx.aborted = 1;
    *out_nodes = ctx.nodes;
    *out_leaf_ops = ctx.leaf_ops;
    *out_num_survivors = ctx.num_survivors;
    return ctx.aborted;
}

HENSEL_EXPORT int run_hensel_standard_u128_ex_c(
    const u384_io *n0_io,
    const u384_io *b1_io,
    const u384_io *b2_io,
    int max_r,
    int include_r0,
    int max_survivors_cap,
    u64 ulam_q126,
    int num_bands,
    const BandIO *bands,
    const int *kd_lo,
    const int *kd_hi,
    u64 max_budget,
    u64 *out_nodes,
    u64 *out_leaf_ops,
    int *out_num_survivors,
    u384_io *out_survivors
) {
    ensure_stack_committed_win64();
    return run_hensel_standard_u128_ex_impl(
        n0_io, b1_io, b2_io, max_r, include_r0, max_survivors_cap, ulam_q126,
        num_bands, bands, kd_lo, kd_hi, max_budget,
        out_nodes, out_leaf_ops, out_num_survivors, out_survivors
    );
}

HENSEL_EXPORT int run_hensel_standard_u128_c(
    const u384_io *n0_io,
    const u384_io *b1_io,
    const u384_io *b2_io,
    int max_r,
    int num_bands,
    const BandIO *bands,
    const int *kd_lo,
    const int *kd_hi,
    u64 max_budget,
    u64 *out_nodes,
    u64 *out_leaf_ops,
    int *out_num_survivors,
    u384_io *out_survivors
) {
    return run_hensel_standard_u128_ex_c(
        n0_io, b1_io, b2_io, max_r, 0, MAX_SURVIVORS, 0ULL,
        num_bands, bands, kd_lo, kd_hi, max_budget,
        out_nodes, out_leaf_ops, out_num_survivors, out_survivors
    );
}

typedef struct {
    HenselCtx base;
    int exact_r;
    int kd_lo_monotone;
    int has_tight_win;
    u128 floor_lo[10];
    u128 ceil_hi[10];
    int ceil_hi_bl[10];
    u64 cong_checks;
    int root_k1;
    u64 lam_lo_q126;
    u64 ulam_hi_q126;
    u64 step_lb_q126[11];
    u64 tail_ub_q126[11];
    u64 tail_lb_q126[11];
    int min_ceil_idx[11];
    int step_kd[11];
    int step_k_exp[11];
    int step_w_exp[11];
    u256f step_g_val[11];
} EscStdCtx;

static inline void verify_z1_esc_u128(EscStdCtx *ectx, u128 z) {
    HenselCtx *ctx = &ectx->base;
    if (ctx->aborted) return;
    if (((u64)z & 1ULL) == 0ULL || z <= (u128)ctx->n0_threshold) return;
    u128 b_hi_128 = (u128)ctx->b_hi;
    u128 cur = z;
    int ex_r = ectx->exact_r;
    for (int step = 1; step <= ex_r; step++) {
        u128 nxt = 0;
        if (next_spiral_u128_check(cur, b_hi_128, &nxt)) return;
        if (nxt < ectx->floor_lo[step - 1] || nxt > ectx->ceil_hi[step - 1]) return;
        cur = nxt;
    }
    u128 dummy_nxt = 0;
    if (next_spiral_u128_check(cur, b_hi_128, &dummy_nxt)) {
        add_survivor(ctx, (u384)z);
    }
}

static inline void test_cong_esc_u128(
    EscStdCtx *ectx,
    u128 diff128,
    int m_exp,
    u128 l1_128,
    u128 u1_128,
    u128 span128
) {
    HenselCtx *ctx = &ectx->base;
    if (((++ectx->cong_checks) & 3ULL) == 0ULL) {
        ctx->leaf_ops++;
        if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
            ctx->aborted = 1;
            return;
        }
    }
    int m_cap = (m_exp > 126) ? 126 : m_exp;
    if (m_cap >= 1 && ((((u64)l1_128 ^ (u64)diff128) & 1ULL) != 0ULL)) return;
    u128 mm1 = g_mask128[m_cap];
    u128 rem = diff128 & mm1;
    if (rem <= span128) {
        ctx->leaf_ops++;
        if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
            ctx->aborted = 1;
            return;
        }
        u128 step = mm1 + 1;
        u128 f = l1_128 + rem;
        u64 sub_v = 0ULL;
        while (f <= u1_128) {
            if ((sub_v & 7ULL) == 0ULL) {
                ctx->leaf_ops++;
                if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
                    ctx->aborted = 1;
                    return;
                }
            }
            sub_v++;
            verify_z1_esc_u128(ectx, f - 1);
            if (ctx->aborted) return;
            f += step;
        }
    }
}

static inline void test_cong_from_depth_esc_u128(
    EscStdCtx *ectx,
    int depth,
    int k_exp,
    int w_exp,
    u256f g_val,
    u128 lo_p1,
    u128 hi_p1,
    u128 diff128,
    int m_exp,
    u128 l1_128,
    u128 u1_128,
    u128 span128
) {
    HenselCtx *ctx = &ectx->base;
    if (((++ectx->cong_checks) & 3ULL) == 0ULL) {
        ctx->leaf_ops++;
        if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
            ctx->aborted = 1;
            return;
        }
    }
    int m_cap = (m_exp > 126) ? 126 : m_exp;
    if (m_cap >= 1 && ((((u64)l1_128 ^ (u64)diff128) & 1ULL) != 0ULL)) return;
    u128 mm1 = g_mask128[m_cap];
    u128 rem = diff128 & mm1;
    if (rem <= span128) {
        ctx->leaf_ops++;
        if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
            ctx->aborted = 1;
            return;
        }
        u128 step_f = mm1 + 1;
        u128 f = l1_128 + rem;
        if (f > u1_128) return;
        u128 p3w = g_p3_128[w_exp];
        u256f zp1_init = u256f_shr(u256f_add(mul128_to_256f(p3w, f), g_val), k_exp);
        if (u256f_gt_u128(zp1_init, hi_p1)) return;
        u256f step_zp1 = u256f_shl_u128(p3w, m_cap - k_exp);
        int single_step_only = u256f_gt_u128(step_zp1, hi_p1);
        u128 step_zp1_128 = single_step_only ? (u128)0 : step_zp1.lo;
        u128 zp1_128 = zp1_init.lo;
        if (zp1_128 < lo_p1) {
            if (single_step_only || step_zp1_128 == 0) return;
            u128 max_q = (u1_128 - f) >> m_cap;
            if (max_q == 0) return;
            u128 need_dz = lo_p1 - zp1_128;
            u128 q_lo = 1;
            if ((max_q >> 30) == 0 && (need_dz >> 64) == 0 && (step_zp1_128 >> 64) == 0) {
                q_lo = (u128)(((u64)need_dz + (u64)step_zp1_128 - 1ULL) / (u64)step_zp1_128);
                if (q_lo > max_q) return;
            } else if ((max_q >> 24) == 0) {
                int sh_d = bit_length_128(step_zp1_128) - 54;
                if (sh_d < 0) sh_d = 0;
                u64 den_hi = (u64)(step_zp1_128 >> sh_d) + 1ULL;
                u128 num_sh = need_dz >> sh_d;
                if ((num_sh >> 62) != 0) return;
                q_lo = (u128)((u64)num_sh / den_hi);
                if (q_lo < 1) q_lo = 1;
                if (q_lo > max_q) return;
                while (u256f_lt_u128(mul128_to_256f(step_zp1_128, q_lo), need_dz)) {
                    q_lo += 1;
                    if (q_lo > max_q) return;
                }
            } else {
                if (u256f_lt_u128(mul128_to_256f(step_zp1_128, max_q), need_dz)) return;
                u128 q_hi = max_q;
                while (q_lo < q_hi) {
                    u128 q_mid = q_lo + ((q_hi - q_lo) >> 1);
                    if (u256f_lt_u128(mul128_to_256f(step_zp1_128, q_mid), need_dz)) {
                        q_lo = q_mid + 1;
                    } else {
                        q_hi = q_mid;
                    }
                }
            }
            u256f dz256 = mul128_to_256f(step_zp1_128, q_lo);
            if (dz256.hi != 0 || hi_p1 - zp1_128 < dz256.lo) return;
            zp1_128 += dz256.lo;
            f += (q_lo << m_cap);
        }
        u128 b_hi_128 = (u128)ctx->b_hi;
        int ex_r = ectx->exact_r;
        u64 sub_v = 0ULL;
        while (f <= u1_128) {
            if ((sub_v & 7ULL) == 0ULL) {
                ctx->leaf_ops++;
                if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
                    ctx->aborted = 1;
                    return;
                }
            }
            sub_v++;
            if (zp1_128 >= lo_p1) {
                u128 cur = zp1_128 - 1;
                int ok = 1;
                for (int st = depth + 1; st <= ex_r; st++) {
                    u128 nxt = 0;
                    if (next_spiral_u128_check(cur, b_hi_128, &nxt) || nxt < ectx->floor_lo[st - 1] || nxt > ectx->ceil_hi[st - 1]) {
                        ok = 0;
                        break;
                    }
                    cur = nxt;
                }
                if (ok) {
                    u128 dm = 0;
                    if (next_spiral_u128_check(cur, b_hi_128, &dm)) {
                        verify_z1_esc_u128(ectx, f - 1);
                        if (ctx->aborted) return;
                    }
                }
            }
            if (single_step_only) break;
            if (hi_p1 - zp1_128 < step_zp1_128) break;
            zp1_128 += step_zp1_128;
            f += step_f;
        }
    }
}

static const int esc_leaf_bits[12] = {79, 82, 85, 88, 92, 97, 102, 107, 112, 116, 120, 123};
static const int esc_mid_bits[13] = {74, 76, 78, 80, 82, 84, 86, 89, 92, 96, 101, 107, 114};

static inline int eval_aff_yp1_esc(
    int w,
    int k,
    u128 f,
    u256f g,
    u128 *out_fl,
    int *out_gt128,
    u128 *out_rem
) {
    if (w <= 80 && k <= 126) {
        u256f sum = u256f_add(mul128_to_256f(g_p3_128[w], f), g);
        u256f fl = u256f_shr(sum, k);
        *out_gt128 = (fl.hi != 0) ? 1 : 0;
        *out_fl = fl.lo;
        *out_rem = ((sum.lo & g_mask128[k]) != 0) ? (u128)1 : (u128)0;
        return 1;
    }
    if (w <= 185 && k <= 250) {
        u384 g384 = (((u384)g.hi) << 128) | (u384)g.lo;
        u384 sum384 = g_p3[w] * (u384)f + g384;
        u384 fl384 = shr384(sum384, k);
        *out_gt128 = ((fl384 >> 128) != 0) ? 1 : 0;
        *out_fl = (u128)fl384;
        *out_rem = ((sum384 & g_mask384[k]) != 0) ? (u128)1 : (u128)0;
        return 1;
    }
    return 0;
}

static inline int coupled_can_prune_ge_q126(
    const EscStdCtx *ectx,
    int depth,
    int k_cur,
    int w_cur,
    u256f g_cur,
    u128 f
) {
    u64 lim = ectx->lam_lo_q126;
    if (lim == 0ULL) return 0;
    u64 ub = step_term_ub_exact_q126((u384)(f - 1), ectx->root_k1) + ectx->tail_ub_q126[depth];
    if (ub > lim) return 0;
    for (int j = 1; j < depth; j++) {
        u128 yp1_lo = 0, has_rem = 0;
        int gt128 = 0;
        if (!eval_aff_yp1_esc(ectx->step_w_exp[j], ectx->step_k_exp[j], f, ectx->step_g_val[j], &yp1_lo, &gt128, &has_rem)) return 0;
        u128 c_hi_p1 = ectx->ceil_hi[j - 1] + 1;
        if (gt128 || yp1_lo > c_hi_p1) return 1;
        u128 yp1_cl = yp1_lo + has_rem;
        if (yp1_cl > c_hi_p1) return 1;
        u128 c_min = (yp1_cl > 1) ? (yp1_cl - 1) : (u128)1;
        u128 z_min = (c_min > ectx->floor_lo[j - 1]) ? c_min : ectx->floor_lo[j - 1];
        ub += (z_min >= (((u128)1) << 84))
            ? step_term_ub_fast_q126((u384)z_min, ectx->step_kd[j])
            : step_term_ub_exact_q126((u384)z_min, ectx->step_kd[j]);
        if (ub > lim) return 0;
    }
    u128 yp1_d = 0, rem_d = 0;
    int gt_d = 0;
    if (!eval_aff_yp1_esc(w_cur, k_cur, f, g_cur, &yp1_d, &gt_d, &rem_d)) return 0;
    u128 c_hi_d = ectx->ceil_hi[depth - 1] + 1;
    if (gt_d || yp1_d > c_hi_d) return 1;
    u128 ycl_d = yp1_d + rem_d;
    if (ycl_d > c_hi_d) return 1;
    u128 c_min_d = (ycl_d > 1) ? (ycl_d - 1) : (u128)1;
    u128 z_min_d = (c_min_d > ectx->floor_lo[depth - 1]) ? c_min_d : ectx->floor_lo[depth - 1];
    ub += (z_min_d >= (((u128)1) << 84))
        ? inv_z_ub_fast_q126((u384)z_min_d)
        : inv_z_ub_exact_q126((u384)z_min_d);
    return (ub <= lim) ? 1 : 0;
}

static inline int coupled_can_prune_le_q126(
    const EscStdCtx *ectx,
    int depth,
    int k_cur,
    int w_cur,
    u256f g_cur,
    int kd_cur_min,
    u128 f
) {
    u64 lim = ectx->ulam_hi_q126;
    if (lim == 0ULL) return 0;
    u64 lb = step_term_lb_exact_q126((u384)(f - 1), ectx->root_k1) + ectx->tail_lb_q126[depth];
    if (lb >= lim) return 1;
    for (int j = 1; j < depth; j++) {
        u128 yp1_lo = 0, dummy_rem = 0;
        int gt128 = 0;
        if (!eval_aff_yp1_esc(ectx->step_w_exp[j], ectx->step_k_exp[j], f, ectx->step_g_val[j], &yp1_lo, &gt128, &dummy_rem)) return 0;
        if (!gt128 && yp1_lo <= ectx->floor_lo[j - 1]) return 1;
        u128 z_max = (gt128 || (yp1_lo - 1) > ectx->ceil_hi[j - 1])
            ? ectx->ceil_hi[j - 1]
            : (yp1_lo - 1);
        if (ectx->step_kd[j] < 126 && (z_max + 1) < (((u128)1) << ectx->step_kd[j])) return 1;
        lb += (z_max >= (((u128)1) << 84))
            ? step_term_lb_fast_q126((u384)z_max, ectx->step_kd[j])
            : step_term_lb_exact_q126((u384)z_max, ectx->step_kd[j]);
        if (lb >= lim) return 1;
    }
    u128 yp1_d = 0, dummy_d = 0;
    int gt_d = 0;
    if (!eval_aff_yp1_esc(w_cur, k_cur, f, g_cur, &yp1_d, &gt_d, &dummy_d)) return 0;
    if (!gt_d && yp1_d <= ectx->floor_lo[depth - 1]) return 1;
    u128 z_max_d = (gt_d || (yp1_d - 1) > ectx->ceil_hi[depth - 1])
        ? ectx->ceil_hi[depth - 1]
        : (yp1_d - 1);
    int b_zmd = bit_length_128(z_max_d + 1);
    int kd_eff = (depth < ectx->exact_r)
        ? min_kd_for_jump(b_zmd, bit_length_128(ectx->floor_lo[depth]))
        : ectx->base.kd_hi[b_zmd];
    if (kd_eff < kd_cur_min) kd_eff = kd_cur_min;
    if (kd_eff >= b_zmd) return 1;
    lb += (z_max_d >= (((u128)1) << 84))
        ? step_term_lb_fast_q126((u384)z_max_d, kd_eff)
        : step_term_lb_exact_q126((u384)z_max_d, kd_eff);
    return (lb >= lim) ? 1 : 0;
}

/* Returns 0 if entire [io_l1, io_u1] is pruned, 1 if unchanged, 2 if shrunk. */
static inline int shrink_band_coupled_q126(
    EscStdCtx *ectx,
    int depth,
    int k_cur,
    int w_cur,
    u256f g_cur,
    int kd_cur_min,
    u128 *io_l1,
    u128 *io_u1
) {
    HenselCtx *ctx = &ectx->base;
    u128 l = *io_l1;
    u128 u = *io_u1;
    if (((u64)l & 1ULL) != 0ULL) l += 1;
    if (((u64)u & 1ULL) != 0ULL) u -= 1;
    if (l > u) return 0;
    int shrank_l = 0;
    int shrank_u = 0;

    if (ectx->ulam_hi_q126 > 0ULL) {
        ctx->leaf_ops++;
        u128 span = u - l;
        if (span == 0) {
            if (coupled_can_prune_le_q126(ectx, depth, k_cur, w_cur, g_cur, kd_cur_min, l)) return 0;
        } else {
            u128 probe_lo = (l + (span >> ((depth == 1) ? 2 : 1))) & ~(u128)1;
            if (probe_lo < l) probe_lo = l;
            if (probe_lo > u) probe_lo = u;
            if (coupled_can_prune_le_q126(ectx, depth, k_cur, w_cur, g_cur, kd_cur_min, probe_lo)) {
                ctx->leaf_ops++;
                if (coupled_can_prune_le_q126(ectx, depth, k_cur, w_cur, g_cur, kd_cur_min, u)) return 0;
                u128 l_cert = probe_lo;
                u128 bs_lo = probe_lo + 2;
                u128 bs_hi = u - 2;
                for (int it = 0; it < 10 && bs_lo <= bs_hi; it++) {
                    if (bs_hi < u - 2 && (bs_hi - bs_lo) <= ((u - bs_hi) >> 1)) break;
                    ctx->leaf_ops++;
                    u128 mid = (bs_lo + ((bs_hi - bs_lo) >> 1)) & ~(u128)1;
                    if (mid < bs_lo) mid = bs_lo;
                    if (coupled_can_prune_le_q126(ectx, depth, k_cur, w_cur, g_cur, kd_cur_min, mid)) {
                        l_cert = mid;
                        bs_lo = mid + 2;
                    } else {
                        if (mid < 4) break;
                        bs_hi = mid - 2;
                    }
                }
                l = l_cert + 2;
                if (l > u) return 0;
                shrank_l = 1;
            }
        }
    }

    if (ectx->lam_lo_q126 > 0ULL && depth <= 2 && ectx->floor_lo[depth - 1] < (((u128)1) << 82)) {
        ctx->leaf_ops++;
        u128 span = u - l;
        if (span == 0) {
            if (coupled_can_prune_ge_q126(ectx, depth, k_cur, w_cur, g_cur, l)) return 0;
        } else {
            u128 probe_hi = (u - (span >> ((depth == 1) ? 2 : 1))) & ~(u128)1;
            if (probe_hi < l) probe_hi = l;
            if (coupled_can_prune_ge_q126(ectx, depth, k_cur, w_cur, g_cur, probe_hi)) {
                ctx->leaf_ops++;
                if (coupled_can_prune_ge_q126(ectx, depth, k_cur, w_cur, g_cur, l)) return 0;
                u128 u_cert = probe_hi;
                u128 bs_lo = l + 2;
                u128 bs_hi = probe_hi - 2;
                for (int it = 0; it < 10 && bs_lo <= bs_hi; it++) {
                    if (bs_lo > l + 2 && (bs_hi - bs_lo) <= ((bs_lo - l) >> 1)) break;
                    ctx->leaf_ops++;
                    u128 mid = (bs_lo + ((bs_hi - bs_lo) >> 1)) & ~(u128)1;
                    if (mid < bs_lo) mid = bs_lo;
                    if (coupled_can_prune_ge_q126(ectx, depth, k_cur, w_cur, g_cur, mid)) {
                        u_cert = mid;
                        if (mid < 4) break;
                        bs_hi = mid - 2;
                    } else {
                        bs_lo = mid + 2;
                    }
                }
                if (u_cert < 2) return 0;
                u = u_cert - 2;
                if (l > u) return 0;
                shrank_u = 1;
            }
        }
    }

    if (!shrank_l && shrank_u && ectx->ulam_hi_q126 > 0ULL) {
        ctx->leaf_ops++;
        u128 span = u - l;
        if (span == 0) {
            if (coupled_can_prune_le_q126(ectx, depth, k_cur, w_cur, g_cur, kd_cur_min, l)) return 0;
        } else {
            u128 probe_lo = (l + (span >> ((depth == 1) ? 2 : 1))) & ~(u128)1;
            if (probe_lo < l) probe_lo = l;
            if (probe_lo > u) probe_lo = u;
            if (coupled_can_prune_le_q126(ectx, depth, k_cur, w_cur, g_cur, kd_cur_min, probe_lo)) {
                ctx->leaf_ops++;
                if (coupled_can_prune_le_q126(ectx, depth, k_cur, w_cur, g_cur, kd_cur_min, u)) return 0;
                u128 l_cert = probe_lo;
                u128 bs_lo = probe_lo + 2;
                u128 bs_hi = u - 2;
                for (int it = 0; it < 10 && bs_lo <= bs_hi; it++) {
                    if (bs_hi < u - 2 && (bs_hi - bs_lo) <= ((u - bs_hi) >> 1)) break;
                    ctx->leaf_ops++;
                    u128 mid = (bs_lo + ((bs_hi - bs_lo) >> 1)) & ~(u128)1;
                    if (mid < bs_lo) mid = bs_lo;
                    if (coupled_can_prune_le_q126(ectx, depth, k_cur, w_cur, g_cur, kd_cur_min, mid)) {
                        l_cert = mid;
                        bs_lo = mid + 2;
                    } else {
                        if (mid < 4) break;
                        bs_hi = mid - 2;
                    }
                }
                l = l_cert + 2;
                if (l > u) return 0;
                shrank_l = 1;
            }
        }
    }

    if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
        ctx->aborted = 1;
        return 0;
    }
    if (shrank_l || shrank_u) {
        *io_l1 = l;
        *io_u1 = u;
        return 2;
    }
    return 1;
}

static void dfs_std_esc_u128(
    EscStdCtx *ectx,
    int depth,
    int k_exp,
    int w_exp,
    u256f g_val,
    u128 lo_z,
    u128 hi_z,
    u64 rem_ulam,
    u64 req_lam_lo,
    u128 l1_128,
    u128 u1_128,
    u128 span128,
    int k_coll
) {
    HenselCtx *ctx = &ectx->base;
    if (ctx->aborted) return;
    ctx->nodes++;
    if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
        ctx->aborted = 1;
        return;
    }
    if (k_exp + 1 >= k_coll) {
        u128 r128 = ((u128)0 - g_val.lo) * (u128)g_inv3[w_exp];
        test_cong_esc_u128(ectx, r128 - l1_128, k_exp + 1, l1_128, u1_128, span128);
        return;
    }

    u128 hi_p1 = hi_z + 1;
    u128 lo_p1 = lo_z + 1;
    int ex_r = ectx->exact_r;
    if (req_lam_lo > ectx->tail_ub_q126[depth]) {
        u64 deficit_cur = req_lam_lo - ectx->tail_ub_q126[depth];
        u64 max_ub_cur = (lo_p1 > (((u128)1) << 84))
            ? inv_z_ub_fast_q126((u384)(lo_p1 - 1))
            : inv_z_ub_exact_q126((u384)(lo_p1 - 1));
        if (max_ub_cur < deficit_cur) return;
        u128 max_zp1 = pole_max_cur_u128(deficit_cur) + (u128)1;
        if (max_zp1 < lo_p1) return;
        if (max_zp1 < hi_p1) {
            hi_p1 = max_zp1 & ~(u128)1;
            if (hi_p1 < lo_p1) return;
        }
    }
    if (w_exp <= 80 && ctx->u_eff_bl <= 86 && ((g_val.hi >> 122) == 0)) {
        u128 p3w = g_p3_128[w_exp];
        int shrank = 0;
        u256f z_aff_hi = u256f_shr(u256f_add(mul128_to_256f(p3w, u1_128), g_val), k_exp);
        if (u256f_lt_u128(z_aff_hi, lo_p1)) return;
        if (u256f_lt_u128(z_aff_hi, hi_p1)) {
            u128 zh = z_aff_hi.lo;
            if (((u64)zh & 1ULL) != 0ULL) zh -= 1;
            if (zh < lo_p1) return;
            hi_p1 = zh;
        } else if (u256f_gt_u128(z_aff_hi, hi_p1) && k_exp < 126) {
            u256f h_prod = u256f_shl_u128(hi_p1, k_exp);
            if (!u256f_gt(h_prod, g_val)) return;
            u256f x_hi = u256f_sub(h_prod, g_val);
            int xbl = bit_length_256f(x_hi);
            int s_sh = (xbl > 126) ? (xbl - 126) : 0;
            int r_sh = 126 + g_p3_bl[w_exp] - s_sh;
            if (r_sh > 0) {
                u256f u_cand = u256f_shr(mul128_to_256f(u256f_shr(x_hi, s_sh).lo + 1, g_recip3_ub[w_exp]), r_sh);
                if (u256f_lt_u128(u_cand, u1_128)) {
                    u128 u_n = u_cand.lo;
                    if (((u64)u_n & 1ULL) != 0ULL) u_n -= 1;
                    if (u_n < l1_128) return;
                    u1_128 = u_n;
                    shrank = 1;
                }
            }
        }
        u128 m128 = g_mask128[k_exp];
        u256f z_aff_lo = u256f_shr(u256f_add_u128(u256f_add(mul128_to_256f(p3w, l1_128), g_val), m128), k_exp);
        if (u256f_gt_u128(z_aff_lo, hi_p1)) return;
        if (u256f_gt_u128(z_aff_lo, lo_p1)) {
            u128 zl = z_aff_lo.lo;
            if (((u64)zl & 1ULL) != 0ULL) zl += 1;
            if (zl > hi_p1) return;
            lo_p1 = zl;
        } else if (u256f_lt_u128(z_aff_lo, lo_p1) && k_exp < 126) {
            u256f l_prod = u256f_shl_u128(lo_p1, k_exp);
            if (u256f_gt(l_prod, g_val)) {
                u256f x_lo = u256f_sub(l_prod, g_val);
                int xbl = bit_length_256f(x_lo);
                int s_sh = (xbl > 126) ? (xbl - 126) : 0;
                int r_sh = 126 + g_p3_bl[w_exp] - s_sh;
                if (r_sh > 0) {
                    u256f l_cand = u256f_shr(mul128_to_256f(u256f_shr(x_lo, s_sh).lo, g_recip3_lb[w_exp]), r_sh);
                    if (u256f_gt_u128(l_cand, u1_128)) return;
                    if (l_cand.lo > l1_128) {
                        u128 l_n = l_cand.lo;
                        if (((u64)l_n & 1ULL) != 0ULL) l_n += 1;
                        if (l_n > u1_128) return;
                        l1_128 = l_n;
                        shrank = 1;
                    }
                }
            }
        }
        if (shrank) {
            span128 = u1_128 - l1_128;
            k_coll = bit_length_128(span128);
            if (k_coll < 1) k_coll = 1;
            if (k_exp + 1 >= k_coll) {
                u128 r128 = ((u128)0 - g_val.lo) * (u128)g_inv3[w_exp];
                test_cong_esc_u128(ectx, r128 - l1_128, k_exp + 1, l1_128, u1_128, span128);
                return;
            }
        }
    } else if (w_exp <= 190 && ctx->u_eff_bl <= 86) {
        u384 g384 = (((u384)g_val.hi) << 128) | (u384)g_val.lo;
        u384 p3w384 = g_p3[w_exp];
        int shrank = 0;
        u384 z_aff_hi = shr384(p3w384 * (u384)u1_128 + g384, k_exp);
        if (z_aff_hi < (u384)lo_p1) return;
        if (z_aff_hi < (u384)hi_p1) {
            u128 zh = (u128)z_aff_hi;
            if (((u64)zh & 1ULL) != 0ULL) zh -= 1;
            if (zh < lo_p1) return;
            hi_p1 = zh;
        } else if (z_aff_hi > (u384)hi_p1 && k_exp < 240) {
            u384 h_prod = shl384((u384)hi_p1, k_exp);
            if (h_prod <= g384) return;
            u384 x_hi = h_prod - g384;
            int xbl = bit_length_fast(x_hi);
            int s_sh = (xbl > 126) ? (xbl - 126) : 0;
            int r_sh = 126 + g_p3_bl[w_exp] - s_sh;
            if (r_sh > 0) {
                u128 x_top = (u128)shr384(x_hi, s_sh) + (u128)1;
                u256f u_cand = u256f_shr(mul128_to_256f(x_top, g_recip3_ub[w_exp]), r_sh);
                if (u256f_lt_u128(u_cand, u1_128)) {
                    u128 u_n = u_cand.lo;
                    if (((u64)u_n & 1ULL) != 0ULL) u_n -= 1;
                    if (u_n < l1_128) return;
                    u1_128 = u_n;
                    shrank = 1;
                }
            }
        }
        u384 m384 = (k_exp <= 384) ? g_mask384[k_exp] : ~(u384)0;
        u384 z_aff_lo = shr384(p3w384 * (u384)l1_128 + g384 + m384, k_exp);
        if (z_aff_lo > (u384)hi_p1) return;
        if (z_aff_lo > (u384)lo_p1) {
            u128 zl = (u128)z_aff_lo;
            if (((u64)zl & 1ULL) != 0ULL) zl += 1;
            if (zl > hi_p1) return;
            lo_p1 = zl;
        } else if (z_aff_lo < (u384)lo_p1 && k_exp < 240) {
            u384 l_prod = shl384((u384)lo_p1, k_exp);
            if (l_prod > g384) {
                u384 x_lo = l_prod - g384;
                int xbl = bit_length_fast(x_lo);
                int s_sh = (xbl > 126) ? (xbl - 126) : 0;
                int r_sh = 126 + g_p3_bl[w_exp] - s_sh;
                if (r_sh > 0) {
                    u128 x_top = (u128)shr384(x_lo, s_sh);
                    u256f l_cand = u256f_shr(mul128_to_256f(x_top, g_recip3_lb[w_exp]), r_sh);
                    if (u256f_gt_u128(l_cand, u1_128)) return;
                    if (l_cand.lo > l1_128) {
                        u128 l_n = l_cand.lo;
                        if (((u64)l_n & 1ULL) != 0ULL) l_n += 1;
                        if (l_n > u1_128) return;
                        l1_128 = l_n;
                        shrank = 1;
                    }
                }
            }
        }
        if (shrank) {
            span128 = u1_128 - l1_128;
            k_coll = bit_length_128(span128);
            if (k_coll < 1) k_coll = 1;
            if (k_exp + 1 >= k_coll) {
                u128 r128 = ((u128)0 - g_val.lo) * (u128)g_inv3[w_exp];
                test_cong_esc_u128(ectx, r128 - l1_128, k_exp + 1, l1_128, u1_128, span128);
                return;
            }
        }
    }

    u128 cur_hi = (((u64)(hi_p1 - 1) & 1ULL) != 0ULL) ? (hi_p1 - 1) : (hi_p1 - 2);
    if (rem_ulam != ~0ULL && step_term_lb_u128(cur_hi, 1) >= rem_ulam) return;

    int b_hi_cur = bit_length_128(hi_p1);
    u128 b_hi_128 = (u128)ctx->b_hi;
    u128 two_b_hi_128 = (u128)ctx->two_b_hi;

    if (depth == ex_r) {
        int kd_start = ctx->kd_hi[b_hi_cur];
        if (kd_start >= b_hi_cur) return;
        if (ectx->ulam_hi_q126 > 0ULL && (k_coll - k_exp) >= 6
            && depth <= 2) {
            int sh_rc = shrink_band_coupled_q126(ectx, depth, k_exp, w_exp, g_val, kd_start, &l1_128, &u1_128);
            if (sh_rc == 0) return;
            if (sh_rc == 2) {
                span128 = u1_128 - l1_128;
                k_coll = bit_length_128(span128);
                if (k_coll < 1) k_coll = 1;
                if (k_exp + 1 >= k_coll) {
                    u128 r128 = ((u128)0 - g_val.lo) * (u128)g_inv3[w_exp];
                    test_cong_esc_u128(ectx, r128 - l1_128, k_exp + 1, l1_128, u1_128, span128);
                    return;
                }
            }
        }
        if (k_exp + kd_start + 5 >= k_coll && w_exp <= 80) {
            u128 rc_e = ((u128)0 - g_val.lo) * (u128)g_inv3[w_exp];
            test_cong_from_depth_esc_u128(ectx, depth, k_exp, w_exp, g_val, lo_p1, hi_p1, rc_e - l1_128, k_exp + kd_start, l1_128, u1_128, span128);
            return;
        }
        u128 p3k_g128 = (kd_start <= 80) ? (g_p3_128[kd_start] * g_val.lo) : (u128)0;
        for (int kd = kd_start; kd < b_hi_cur; kd++) {
            ctx->leaf_ops++;
            if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
                ctx->aborted = 1;
                return;
            }
            if (rem_ulam != ~0ULL && step_term_lb_u128(cur_hi, kd) >= rem_ulam) break;
            int s_kkd = k_exp + kd;
            if (s_kkd >= k_coll) {
                u128 rc = ((u128)0 - g_val.lo) * (u128)g_inv3[w_exp];
                test_cong_esc_u128(ectx, rc - l1_128, s_kkd, l1_128, u1_128, span128);
                return;
            }
            if (s_kkd + 5 >= k_coll && w_exp <= 80) {
                u128 rc = ((u128)0 - g_val.lo) * (u128)g_inv3[w_exp];
                test_cong_from_depth_esc_u128(ectx, depth, k_exp, w_exp, g_val, lo_p1, hi_p1, rc - l1_128, s_kkd, l1_128, u1_128, span128);
                return;
            }
            u128 cur_p3g = p3k_g128;
            p3k_g128 += (p3k_g128 << 1);
            if (req_lam_lo > 0ULL) {
                u64 lf_ub = (lo_p1 > (((u128)1) << 84))
                    ? step_term_ub_fast_q126((u384)(lo_p1 - 1), kd)
                    : step_term_ub_exact_q126((u384)(lo_p1 - 1), kd);
                if (lf_ub < req_lam_lo) continue;
            }
            u128 u_max = hi_p1 >> kd;
            if (u_max == 0) continue;
            if (((u64)u_max & 1ULL) == 0ULL) u_max -= 1;
            if (u_max < 1) continue;
            u128 u_min_l = (lo_p1 + g_mask128[kd]) >> kd;
            if (u_min_l > u_max) continue;
            u256f ev_max = u256f_sub1(mul128_to_256f(g_p3_128[kd], u_max));
            if (u256f_le_u128(ev_max, two_b_hi_128)) continue;
            u128 inv_wn = (u128)g_inv3[w_exp + kd];
            u128 bd128 = (((((u128)1) << s_kkd) - cur_p3g) * inv_wn) - l1_128;
            u128 inv_sh = inv_wn << (s_kkd + 1);
            int ld_lim = bit_length_256f(ev_max) - ctx->b_hi_bl + 2;
            u256f z_ev = u256f_shr1(ev_max);
            for (int ld = 1; ld <= ld_lim; ld++, z_ev = u256f_shr1(z_ev)) {
                if (u256f_le_u128(z_ev, b_hi_128)) break;
                int k_n = s_kkd + ld;
                if (k_n >= k_coll) {
                    test_cong_esc_u128(ectx, bd128, k_n, l1_128, u1_128, span128);
                    break;
                }
                test_cong_esc_u128(ectx, bd128 - inv_sh, k_n + 1, l1_128, u1_128, span128);
                inv_sh <<= 1;
                if (ctx->aborted) return;
            }
        }
        return;
    }

    u128 base_nxt_lo = ectx->floor_lo[depth];
    u128 step_b_hi = ectx->ceil_hi[depth];
    int step_b_hi_bl = ectx->ceil_hi_bl[depth];
    int next_is_leaf = (depth + 1 == ex_r);
    int t_star = ectx->min_ceil_idx[depth];
    int kd_start = min_kd_for_jump(b_hi_cur, bit_length_128(base_nxt_lo));
    if (ectx->kd_lo_monotone && ctx->kd_lo != 0 && ctx->kd_lo[b_hi_cur] > kd_start) kd_start = ctx->kd_lo[b_hi_cur];
    if (kd_start >= b_hi_cur) return;
    if (rem_ulam != ~0ULL) {
        u64 lb0 = step_term_lb_u128(cur_hi, kd_start);
        if ((lb0 + ectx->tail_lb_q126[depth]) >= rem_ulam) return;
        u64 max_nxt_rem = rem_ulam - lb0;
        u128 p_nxt0 = pole_min_next_u128(max_nxt_rem - ectx->tail_lb_q126[depth + 1]);
        if (p_nxt0 > step_b_hi) return;
        if (t_star != depth) {
            u64 avail_ts0 = max_nxt_rem - (ectx->tail_lb_q126[depth] - ectx->step_lb_q126[t_star]);
            if (pole_min_next_u128(avail_ts0) > ectx->ceil_hi[t_star]) return;
        }
        if (p_nxt0 > base_nxt_lo) {
            base_nxt_lo = p_nxt0;
            int kd2 = min_kd_for_jump(b_hi_cur, bit_length_128(base_nxt_lo));
            if (kd2 > kd_start) {
                kd_start = kd2;
                if (kd_start >= b_hi_cur) return;
                u64 lb2 = step_term_lb_u128(cur_hi, kd_start);
                if ((lb2 + ectx->tail_lb_q126[depth]) >= rem_ulam) return;
            }
        }
    }
    int run_sh = ((ectx->lam_lo_q126 > 0ULL && depth <= 2 && ectx->floor_lo[depth - 1] < (((u128)1) << 82))
            || (ectx->ulam_hi_q126 > 0ULL && (depth == 1 || lo_p1 <= (((u128)1) << 85))))
        && (k_coll - k_exp) >= 6
        && (depth == 1
            || (depth == 2 && w_exp <= 80 && k_exp <= 126 && (k_coll - k_exp) >= 8)
            || (depth == 3 && w_exp <= 80 && k_exp <= 126 && (k_coll - k_exp) >= 14));
    if (run_sh) {
        int sh_rc = shrink_band_coupled_q126(ectx, depth, k_exp, w_exp, g_val, kd_start, &l1_128, &u1_128);
        if (sh_rc == 0) return;
        if (sh_rc == 2) {
            span128 = u1_128 - l1_128;
            k_coll = bit_length_128(span128);
            if (k_coll < 1) k_coll = 1;
            if (k_exp + 1 >= k_coll) {
                u128 r128 = ((u128)0 - g_val.lo) * (u128)g_inv3[w_exp];
                test_cong_esc_u128(ectx, r128 - l1_128, k_exp + 1, l1_128, u1_128, span128);
                return;
            }
            if (w_exp <= 80 && k_exp <= 80) {
                u128 p3w = g_p3_128[w_exp];
                u256f z_aff_hi = u256f_shr(u256f_add(mul128_to_256f(p3w, u1_128), g_val), k_exp);
                if (u256f_lt_u128(z_aff_hi, lo_p1)) return;
                if (u256f_lt_u128(z_aff_hi, hi_p1)) {
                    u128 zh = z_aff_hi.lo;
                    if (((u64)zh & 1ULL) != 0ULL) zh -= 1;
                    if (zh < lo_p1) return;
                    hi_p1 = zh;
                }
                u256f z_aff_lo = u256f_shr(u256f_add_u128(u256f_add(mul128_to_256f(p3w, l1_128), g_val), g_mask128[k_exp]), k_exp);
                if (u256f_gt_u128(z_aff_lo, hi_p1)) return;
                if (u256f_gt_u128(z_aff_lo, lo_p1)) {
                    u128 zl = z_aff_lo.lo;
                    if (((u64)zl & 1ULL) != 0ULL) zl += 1;
                    if (zl > hi_p1) return;
                    lo_p1 = zl;
                }
                cur_hi = (((u64)(hi_p1 - 1) & 1ULL) != 0ULL) ? (hi_p1 - 1) : (hi_p1 - 2);
                b_hi_cur = bit_length_128(hi_p1);
                kd_start = min_kd_for_jump(b_hi_cur, bit_length_128(base_nxt_lo));
                if (ectx->kd_lo_monotone && ctx->kd_lo != 0 && ctx->kd_lo[b_hi_cur] > kd_start) kd_start = ctx->kd_lo[b_hi_cur];
                if (kd_start >= b_hi_cur) return;
            } else if (w_exp <= 190 && k_exp <= 240) {
                u384 g384 = (((u384)g_val.hi) << 128) | (u384)g_val.lo;
                u384 p3w384 = g_p3[w_exp];
                u384 z_aff_hi = shr384(p3w384 * (u384)u1_128 + g384, k_exp);
                if (z_aff_hi < (u384)lo_p1) return;
                if (z_aff_hi < (u384)hi_p1) {
                    u128 zh = (u128)z_aff_hi;
                    if (((u64)zh & 1ULL) != 0ULL) zh -= 1;
                    if (zh < lo_p1) return;
                    hi_p1 = zh;
                }
                u384 m384 = g_mask384[k_exp];
                u384 z_aff_lo = shr384(p3w384 * (u384)l1_128 + g384 + m384, k_exp);
                if (z_aff_lo > (u384)hi_p1) return;
                if (z_aff_lo > (u384)lo_p1) {
                    u128 zl = (u128)z_aff_lo;
                    if (((u64)zl & 1ULL) != 0ULL) zl += 1;
                    if (zl > hi_p1) return;
                    lo_p1 = zl;
                }
                cur_hi = (((u64)(hi_p1 - 1) & 1ULL) != 0ULL) ? (hi_p1 - 1) : (hi_p1 - 2);
                b_hi_cur = bit_length_128(hi_p1);
                kd_start = min_kd_for_jump(b_hi_cur, bit_length_128(base_nxt_lo));
                if (ectx->kd_lo_monotone && ctx->kd_lo != 0 && ctx->kd_lo[b_hi_cur] > kd_start) kd_start = ctx->kd_lo[b_hi_cur];
                if (kd_start >= b_hi_cur) return;
            }
        }
    }
    if (rem_ulam != ~0ULL && (step_term_lb_u128(cur_hi, kd_start) + ectx->tail_lb_q126[depth]) >= rem_ulam) return;
    int e_gap = next_is_leaf ? 4 : 3;
    if (k_exp + kd_start + e_gap >= k_coll && w_exp < 350) {
        u128 rc_e = ((u128)0 - g_val.lo) * (u128)g_inv3[w_exp];
        if (w_exp <= 80) {
            test_cong_from_depth_esc_u128(ectx, depth, k_exp, w_exp, g_val, lo_p1, hi_p1, rc_e - l1_128, k_exp + kd_start, l1_128, u1_128, span128);
        } else {
            test_cong_esc_u128(ectx, rc_e - l1_128, k_exp + kd_start, l1_128, u1_128, span128);
        }
        return;
    }
    u128 p3k_g_lo = (kd_start <= 80) ? (g_p3_128[kd_start] * g_val.lo) : (u128)0;

    for (int kd = kd_start; kd < b_hi_cur; kd++) {
        if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
            ctx->aborted = 1;
            return;
        }
        u64 nxt_rem = rem_ulam;
        if (rem_ulam != ~0ULL) {
            u64 cur_lb = step_term_lb_u128(cur_hi, kd);
            if ((cur_lb + ectx->tail_lb_q126[depth]) >= rem_ulam) break;
            nxt_rem = rem_ulam - cur_lb;
        }
        int s_kkd = k_exp + kd;
        if (s_kkd >= k_coll) {
            u128 rc = ((u128)0 - g_val.lo) * (u128)g_inv3[w_exp];
            test_cong_esc_u128(ectx, rc - l1_128, s_kkd, l1_128, u1_128, span128);
            break;
        }
        u128 eff_b_lo = base_nxt_lo;
        if (rem_ulam != ~0ULL) {
            u128 p_nxt = pole_min_next_u128(nxt_rem - ectx->tail_lb_q126[depth + 1]);
            if (p_nxt > step_b_hi) break;
            if (p_nxt > eff_b_lo) eff_b_lo = p_nxt;
            if (t_star != depth) {
                u64 avail_ts = nxt_rem - (ectx->tail_lb_q126[depth] - ectx->step_lb_q126[t_star]);
                if (pole_min_next_u128(avail_ts) > ectx->ceil_hi[t_star]) break;
            }
        }
        if (eff_b_lo > step_b_hi) break;
        if (eff_b_lo > base_nxt_lo && kd < min_kd_for_jump(b_hi_cur, bit_length_128(eff_b_lo))) {
            p3k_g_lo += (p3k_g_lo << 1);
            continue;
        }
        if (s_kkd + e_gap >= k_coll && w_exp <= 80) {
            u128 rc = ((u128)0 - g_val.lo) * (u128)g_inv3[w_exp];
            test_cong_from_depth_esc_u128(ectx, depth, k_exp, w_exp, g_val, lo_p1, hi_p1, rc - l1_128, s_kkd, l1_128, u1_128, span128);
            break;
        }
        u128 cur_p3g_lo = p3k_g_lo;
        p3k_g_lo += (p3k_g_lo << 1);

        u128 u_min = (lo_p1 + g_mask128[kd]) >> kd;
        if (u_min < 1) u_min = 1;
        if (((u64)u_min & 1ULL) == 0ULL) u_min += 1;
        u128 u_max = hi_p1 >> kd;
        if (u_max < u_min) continue;
        if (((u64)u_max & 1ULL) == 0ULL) u_max -= 1;
        if (u_min > u_max) continue;

        u128 p3_kd = g_p3_128[kd];
        u256f ev_max = u256f_sub1(mul128_to_256f(p3_kd, u_max));
        u128 two_eff_blo = eff_b_lo << 1;
        if (u256f_lt_u128(ev_max, two_eff_blo)) continue;
        u256f ev_min = u256f_sub1(mul128_to_256f(p3_kd, u_min));
        u128 kd_lo_p1 = lo_p1;
        if (u256f_lt_u128(ev_min, two_eff_blo)) {
            if (kd <= 80) {
                u128 u_lb = u256f_shr(mul128_to_256f(two_eff_blo, g_recip3_lb[kd]), 126 + g_p3_bl[kd]).lo + (u128)1;
                if (((u64)u_lb & 1ULL) == 0ULL) u_lb += (u128)1;
                if (u_lb > u_min) {
                    if (u_lb > u_max) continue;
                    u_min = u_lb;
                    u128 cand_lo_p1 = u_min << kd;
                    if (cand_lo_p1 > kd_lo_p1) kd_lo_p1 = cand_lo_p1;
                }
            }
            ev_min.lo = two_eff_blo;
            ev_min.hi = 0;
        }

        u64 nxt_req_lam = 0ULL;
        u128 eff_b_hi = step_b_hi;
        int eff_b_hi_bl = step_b_hi_bl;
        if (req_lam_lo > 0ULL) {
            u64 cur_ub = (kd_lo_p1 > (((u128)1) << 84))
                ? step_term_ub_fast_q126((u384)(kd_lo_p1 - 1), kd)
                : step_term_ub_exact_q126((u384)(kd_lo_p1 - 1), kd);
            if ((cur_ub + ectx->tail_ub_q126[depth]) < req_lam_lo) continue;
            nxt_req_lam = (req_lam_lo > cur_ub) ? (req_lam_lo - cur_ub) : 0ULL;
            if (nxt_req_lam > ectx->tail_ub_q126[depth + 1]) {
                u128 p_mx = pole_max_cur_u128(nxt_req_lam - ectx->tail_ub_q126[depth + 1]);
                if (p_mx < eff_b_lo) continue;
                if (p_mx < eff_b_hi) {
                    eff_b_hi = (((u64)p_mx & 1ULL) != 0ULL) ? p_mx : (p_mx - 1);
                    if (eff_b_lo > eff_b_hi) continue;
                    eff_b_hi_bl = bit_length_128(eff_b_hi);
                }
            }
        }
        int ld_start = bit_length_256f(ev_min) - eff_b_hi_bl;
        if (ld_start < 1) ld_start = 1;
        if (u256f_gt_u128(u256f_shr(ev_min, ld_start), eff_b_hi)) ld_start += 1;
        int ld_end = bit_length_256f(ev_max) - bit_length_128(eff_b_lo) + 1;
        if (ld_start > ld_end) continue;
        u256f z_mx = u256f_shr(ev_max, ld_start);
        if (u256f_lt_u128(z_mx, eff_b_lo)) continue;

        int w_n = w_exp + kd;
        u128 inv_wn = (u128)g_inv3[w_n];
        u128 sh_kkd_128 = ((u128)1) << s_kkd;
        u128 base_diff_128 = ((sh_kkd_128 - cur_p3g_lo) * inv_wn) - l1_128;
        int have_p3g = 0;
        u256f p3k_g_full = {(u128)0, (u128)0};

        if (next_is_leaf) {
            u256f z_mn = u256f_shr(ev_min, ld_start);
            for (int ld = ld_start; ld <= ld_end; ld++, z_mx = u256f_shr1(z_mx), z_mn = u256f_shr1(z_mn)) {
                if (u256f_lt_u128(z_mx, eff_b_lo)) break;
                if (u256f_gt_u128(z_mn, eff_b_hi)) continue;
                int k_n = s_kkd + ld;
                if (k_n >= k_coll) {
                    test_cong_esc_u128(ectx, base_diff_128, k_n, l1_128, u1_128, span128);
                    break;
                }
                u128 cur_inv = inv_wn << k_n;
                u128 n_hi = u256f_le_u128(z_mx, eff_b_hi)
                    ? ((((u64)z_mx.lo & 1ULL) != 0ULL) ? z_mx.lo : (z_mx.lo - 1))
                    : eff_b_hi;
                u128 n_lo = u256f_le_u128(z_mn, eff_b_lo) ? eff_b_lo : (z_mn.lo | (u128)1);
                if (n_lo > n_hi) continue;
                int b_nhi = bit_length_128(n_hi + 1);
                int ks = ctx->kd_hi[b_nhi];
                if (ks >= b_nhi) continue;
                int s_exp = k_n + ks;
                if (s_exp >= k_coll) {
                    test_cong_esc_u128(ectx, base_diff_128 - cur_inv, s_exp, l1_128, u1_128, span128);
                } else {
                    int b_nlo = bit_length_128(n_lo + 1);
                    int ks_max_lf = ctx->kd_hi[b_nlo];
                    if ((((!ectx->has_tight_win || nxt_req_lam == 0ULL || b_nlo >= 82) && b_nlo >= 80)
                            || ((b_nhi - b_nlo <= 2) && (nxt_req_lam == 0ULL || b_nlo >= 80)))
                        && (k_n + ks_max_lf) < k_coll
                        && (nxt_rem == ~0ULL || step_term_lb_u128(n_lo, ks_max_lf) < nxt_rem)) {
                        if (!have_p3g) {
                            p3k_g_full = u256f_mul_u128(g_val, p3_kd);
                            have_p3g = 1;
                        }
                        u256f g_n = u256f_add_u128(p3k_g_full, (((u128)1) << k_n) - sh_kkd_128);
                        ectx->step_kd[depth] = kd;
                        ectx->step_k_exp[depth] = k_exp;
                        ectx->step_w_exp[depth] = w_exp;
                        ectx->step_g_val[depth] = g_val;
                        dfs_std_esc_u128(ectx, depth + 1, k_n, w_n, g_n, n_lo, n_hi, nxt_rem, nxt_req_lam, l1_128, u1_128, span128, k_coll);
                        if (ctx->aborted) return;
                    } else {
                        int min_s_coll = 1000;
                        int have_gn_lf = 0;
                        u256f g_n = {(u128)0, (u128)0};
                        u128 s_cur = n_lo;
                        for (int ci = 0; ci <= 12 && s_cur <= n_hi; ci++) {
                            u128 cut_hi = (ci < 12) ? ((((u128)1) << esc_leaf_bits[ci]) - 1) : n_hi;
                            u128 s_hi = (cut_hi < n_hi) ? cut_hi : n_hi;
                            if (s_hi < s_cur) continue;
                            int b_shi = bit_length_128(s_hi + 1);
                            int ks_sub = ctx->kd_hi[b_shi];
                            if (ks_sub < b_shi) {
                                int se_sub = k_n + ks_sub;
                                if (se_sub >= k_coll) {
                                    if (se_sub < min_s_coll) min_s_coll = se_sub;
                                } else {
                                    if ((!ectx->has_tight_win || nxt_req_lam == 0ULL || s_cur >= (((u128)1) << 82))
                                        && s_cur >= (((u128)1) << 80)) {
                                        s_hi = n_hi;
                                        b_shi = bit_length_128(s_hi + 1);
                                        ks_sub = ctx->kd_hi[b_shi];
                                    }
                                    if (ks_sub < b_shi && (nxt_rem == ~0ULL || step_term_lb_u128(s_hi, ks_sub) < nxt_rem)) {
                                        if (!have_gn_lf) {
                                            if (!have_p3g) {
                                                p3k_g_full = u256f_mul_u128(g_val, p3_kd);
                                                have_p3g = 1;
                                            }
                                            g_n = u256f_add_u128(p3k_g_full, (((u128)1) << k_n) - sh_kkd_128);
                                            have_gn_lf = 1;
                                        }
                                        ectx->step_kd[depth] = kd;
                                        ectx->step_k_exp[depth] = k_exp;
                                        ectx->step_w_exp[depth] = w_exp;
                                        ectx->step_g_val[depth] = g_val;
                                        dfs_std_esc_u128(ectx, depth + 1, k_n, w_n, g_n, s_cur, s_hi, nxt_rem, nxt_req_lam, l1_128, u1_128, span128, k_coll);
                                        if (ctx->aborted) return;
                                    }
                                }
                            }
                            if (ci == 12 || s_hi >= n_hi) break;
                            s_cur = s_hi + 2;
                        }
                        if (min_s_coll < 1000) {
                            test_cong_esc_u128(ectx, base_diff_128 - cur_inv, min_s_coll, l1_128, u1_128, span128);
                            if (ctx->aborted) return;
                        }
                    }
                }
            }
        } else {
            u256f z_mn = u256f_shr(ev_min, ld_start);
            int nxt2_fl_bl = bit_length_128(ectx->floor_lo[depth + 1]);
            for (int ld = ld_start; ld <= ld_end; ld++, z_mx = u256f_shr1(z_mx), z_mn = u256f_shr1(z_mn)) {
                if (u256f_lt_u128(z_mx, eff_b_lo)) break;
                if (u256f_gt_u128(z_mn, eff_b_hi)) continue;
                int k_n = s_kkd + ld;
                if (k_n >= k_coll) {
                    test_cong_esc_u128(ectx, base_diff_128, k_n, l1_128, u1_128, span128);
                    break;
                }
                u128 n_hi = u256f_le_u128(z_mx, eff_b_hi)
                    ? ((((u64)z_mx.lo & 1ULL) != 0ULL) ? z_mx.lo : (z_mx.lo - 1))
                    : eff_b_hi;
                u128 n_lo = u256f_le_u128(z_mn, eff_b_lo) ? eff_b_lo : (z_mn.lo | (u128)1);
                if (n_lo <= n_hi) {
                    int b_nhi_nxt = bit_length_128(n_hi + 1);
                    int ks_nxt = min_kd_for_jump(b_nhi_nxt, nxt2_fl_bl);
                    if (ectx->kd_lo_monotone && ctx->kd_lo != 0 && ctx->kd_lo[b_nhi_nxt] > ks_nxt) ks_nxt = ctx->kd_lo[b_nhi_nxt];
                    if (ks_nxt >= b_nhi_nxt) continue;
                    int s_exp_nxt = k_n + ks_nxt;
                    if (s_exp_nxt >= k_coll) {
                        test_cong_esc_u128(ectx, base_diff_128 - (inv_wn << k_n), s_exp_nxt, l1_128, u1_128, span128);
                        if (ctx->aborted) return;
                    } else {
                        if (nxt_rem != ~0ULL && (step_term_lb_u128(n_hi, ks_nxt) + ectx->tail_lb_q126[depth + 1]) >= nxt_rem) continue;
                        int b_nlo_m = bit_length_128(n_lo + 1);
                        int ks_max_m = min_kd_for_jump(b_nlo_m, nxt2_fl_bl);
                        if (ectx->kd_lo_monotone && ctx->kd_lo != 0 && ctx->kd_lo[b_nlo_m] > ks_max_m) ks_max_m = ctx->kd_lo[b_nlo_m];
                        if ((((!ectx->has_tight_win || nxt_req_lam == 0ULL || b_nlo_m >= 82) && b_nlo_m >= (depth >= 2 ? 80 : 82))
                                || ((b_nhi_nxt - b_nlo_m <= (b_nlo_m < 84 ? 1 : 2)) && (nxt_req_lam == 0ULL || b_nlo_m >= 80)))
                            && (k_n + ks_max_m) < k_coll
                            && (nxt_rem == ~0ULL || (step_term_lb_u128(n_lo, ks_max_m) + ectx->tail_lb_q126[depth + 1]) < nxt_rem)) {
                            if (!have_p3g) {
                                p3k_g_full = u256f_mul_u128(g_val, p3_kd);
                                have_p3g = 1;
                            }
                            u256f g_n = u256f_add_u128(p3k_g_full, (((u128)1) << k_n) - sh_kkd_128);
                            ectx->step_kd[depth] = kd;
                            ectx->step_k_exp[depth] = k_exp;
                            ectx->step_w_exp[depth] = w_exp;
                            ectx->step_g_val[depth] = g_val;
                            dfs_std_esc_u128(ectx, depth + 1, k_n, w_n, g_n, n_lo, n_hi, nxt_rem, nxt_req_lam, l1_128, u1_128, span128, k_coll);
                            if (ctx->aborted) return;
                        } else {
                            int min_s_coll = 1000;
                            int have_gn_nl = 0;
                            u256f g_n = {(u128)0, (u128)0};
                            u128 s_cur = n_lo;
                            for (int ci = 0; ci <= 13 && s_cur <= n_hi; ci++) {
                                u128 cut_hi = (ci < 13 && ((ectx->has_tight_win && nxt_req_lam > 0ULL && s_cur < (((u128)1) << 82)) || esc_mid_bits[ci] < nxt2_fl_bl || esc_mid_bits[ci] <= 86))
                                    ? ((((u128)1) << esc_mid_bits[ci]) - 1)
                                    : n_hi;
                                u128 s_hi = (cut_hi < n_hi) ? cut_hi : n_hi;
                                if (s_hi < s_cur) continue;
                                int b_shi = bit_length_128(s_hi + 1);
                                int ks_sub = min_kd_for_jump(b_shi, nxt2_fl_bl);
                                if (ectx->kd_lo_monotone && ctx->kd_lo != 0 && ctx->kd_lo[b_shi] > ks_sub) ks_sub = ctx->kd_lo[b_shi];
                                if (ks_sub < b_shi) {
                                    int se_sub = k_n + ks_sub;
                                    if (se_sub >= k_coll) {
                                        if (se_sub < min_s_coll) min_s_coll = se_sub;
                                    } else {
                                        if ((!ectx->has_tight_win || nxt_req_lam == 0ULL || s_cur >= (((u128)1) << 82)) && s_cur >= (((u128)1) << (depth >= 2 ? 80 : 82))) {
                                            s_hi = n_hi;
                                            b_shi = bit_length_128(s_hi + 1);
                                            ks_sub = min_kd_for_jump(b_shi, nxt2_fl_bl);
                                            if (ectx->kd_lo_monotone && ctx->kd_lo != 0 && ctx->kd_lo[b_shi] > ks_sub) ks_sub = ctx->kd_lo[b_shi];
                                        }
                                        if (ks_sub < b_shi && (nxt_rem == ~0ULL || (step_term_lb_u128(s_hi, ks_sub) + ectx->tail_lb_q126[depth + 1]) < nxt_rem)) {
                                            if (!have_gn_nl) {
                                                if (!have_p3g) {
                                                    p3k_g_full = u256f_mul_u128(g_val, p3_kd);
                                                    have_p3g = 1;
                                                }
                                                g_n = u256f_add_u128(p3k_g_full, (((u128)1) << k_n) - sh_kkd_128);
                                                have_gn_nl = 1;
                                            }
                                            ectx->step_kd[depth] = kd;
                                            ectx->step_k_exp[depth] = k_exp;
                                            ectx->step_w_exp[depth] = w_exp;
                                            ectx->step_g_val[depth] = g_val;
                                            dfs_std_esc_u128(ectx, depth + 1, k_n, w_n, g_n, s_cur, s_hi, nxt_rem, nxt_req_lam, l1_128, u1_128, span128, k_coll);
                                            if (ctx->aborted) return;
                                        }
                                    }
                                }
                                if (ci == 13 || s_hi >= n_hi) break;
                                s_cur = s_hi + 2;
                            }
                            if (min_s_coll < 1000) {
                                test_cong_esc_u128(ectx, base_diff_128 - (inv_wn << k_n), min_s_coll, l1_128, u1_128, span128);
                                if (ctx->aborted) return;
                            }
                        }
                    }
                }
            }
        }
    }
}

__attribute__((noinline)) static int run_hensel_win_escalating_impl(
    const u384_io *n0_io,
    const u384_io *w_lo_io,
    const u384_io *w_hi_io,
    const u384_io *b2_io,
    int exact_r,
    int max_survivors_cap,
    u64 ulam_q126,
    u64 lam_lo_q126,
    int num_bands,
    const BandIO *bands,
    const int *kd_lo,
    const int *kd_hi,
    u64 max_budget,
    u64 *out_nodes,
    u64 *out_leaf_ops,
    int *out_num_survivors,
    u384_io *out_survivors
) {
    ensure_q126_tables();
    u384 n0_v = load_u384(n0_io);
    u384 b2_v = load_u384(b2_io);
    if (bit_length_fast(b2_v) > 126 || exact_r < 1 || exact_r > 9) return -6;
    EscStdCtx ectx;
    HenselCtx *ctx = &ectx.base;
    ectx.exact_r = exact_r;
    ectx.kd_lo_monotone = 1;
    ectx.has_tight_win = 0;
    ectx.lam_lo_q126 = lam_lo_q126;
    ectx.ulam_hi_q126 = ulam_q126;
    u384 b_hi_glob = (((u64)b2_v & 1ULL) != 0ULL) ? b2_v : (b2_v - 1);
    u128 b_hi_128 = (u128)b_hi_glob;
    for (int d = 0; d < exact_r; d++) {
        u384 wl_v = load_u384(&w_lo_io[d]);
        if (bit_length_fast(wl_v) > 126) return -6;
        ectx.floor_lo[d] = ((u128)wl_v) | (u128)1;
        if (d > 0 && ectx.floor_lo[d] < ectx.floor_lo[0]) ectx.kd_lo_monotone = 0;
        if (w_hi_io != 0) {
            u384 wh_v = load_u384(&w_hi_io[d]);
            if (bit_length_fast(wh_v) > 126) wh_v = b_hi_glob;
            u128 wh128 = (u128)wh_v;
            if (wh128 > b_hi_128) wh128 = b_hi_128;
            if (((u64)wh128 & 1ULL) == 0ULL && wh128 > 0) wh128 -= 1;
            ectx.ceil_hi[d] = wh128;
        } else {
            ectx.ceil_hi[d] = b_hi_128;
        }
        if (ectx.floor_lo[d] > ectx.ceil_hi[d]) {
            *out_nodes = 0;
            *out_leaf_ops = 0;
            *out_num_survivors = 0;
            return 0;
        }
        ectx.ceil_hi_bl[d] = bit_length_128(ectx.ceil_hi[d]);
        if (lam_lo_q126 > 0ULL && ectx.floor_lo[d] < (((u128)1) << 79)) {
            ectx.has_tight_win = 1;
        }
    }
    ectx.tail_ub_q126[exact_r] = 0ULL;
    ectx.tail_lb_q126[exact_r] = 0ULL;
    for (int s = exact_r - 1; s >= 0; s--) {
        u64 step_ub = inv_z_ub_exact_q126((u384)ectx.floor_lo[s]);
        int c_bl = bit_length_128(ectx.ceil_hi[s] + 1);
        int kd_min_s = (s + 1 < exact_r)
            ? min_kd_for_jump(c_bl, bit_length_128(ectx.floor_lo[s + 1]))
            : kd_hi[c_bl];
        if (ectx.kd_lo_monotone && kd_lo != 0 && kd_lo[c_bl] > kd_min_s) kd_min_s = kd_lo[c_bl];
        if (kd_min_s < 1) kd_min_s = 1;
        u64 step_lb = (kd_min_s < c_bl) ? step_term_lb_exact_q126((u384)ectx.ceil_hi[s], kd_min_s) : 0ULL;
        ectx.step_lb_q126[s] = step_lb;
        ectx.tail_ub_q126[s] = ectx.tail_ub_q126[s + 1] + step_ub;
        ectx.tail_lb_q126[s] = ectx.tail_lb_q126[s + 1] + step_lb;
        if (s == exact_r - 1) {
            ectx.min_ceil_idx[s] = s;
        } else {
            int prev_m = ectx.min_ceil_idx[s + 1];
            ectx.min_ceil_idx[s] = (ectx.ceil_hi[s] <= ectx.ceil_hi[prev_m]) ? s : prev_m;
        }
    }
    ctx->n0_threshold = n0_v;
    ctx->b_lo = (u384)ectx.floor_lo[0];
    ctx->b_hi = b_hi_glob;
    ctx->two_b_lo = 2 * ctx->b_lo;
    ctx->two_b_hi = 2 * b2_v;
    ctx->b_lo_bl = bit_length_fast(ctx->b_lo);
    ctx->b_hi_bl = bit_length_fast(b2_v);
    ctx->cur_r = exact_r;
    ctx->max_r_verify = exact_r;
    ctx->kd_lo = kd_lo;
    ctx->kd_hi = kd_hi;
    ctx->is_windowed = 0;
    ctx->is_two_vertex = 0;
    ctx->bridge_to_x2 = 0;
    ctx->nodes = 0;
    ctx->leaf_ops = 0;
    ectx.cong_checks = 0;
    ctx->max_budget = max_budget;
    ctx->aborted = 0;
    ctx->max_survivors = (max_survivors_cap > 0) ? max_survivors_cap : MAX_SURVIVORS;
    ctx->num_survivors = 0;
    ctx->out_survivors = out_survivors;

    u128 b_lo_0 = ectx.floor_lo[0];
    u128 b_hi_0 = ectx.ceil_hi[0];
    int b_hi_0_bl = ectx.ceil_hi_bl[0];

    for (int b = 0; b < num_bands; b++) {
        if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
            ctx->aborted = 1;
            break;
        }
        int k1 = bands[b].k1;
        if (k1 < 1 || k1 >= 120) return -5;
        ectx.root_k1 = k1;
        u384 lo1 = load_u384(&bands[b].lo1);
        u384 hi1 = load_u384(&bands[b].hi1);
        u384 u_min = load_u384(&bands[b].u_min);
        u384 u_max = load_u384(&bands[b].u_max);
        if (lo1 > hi1 || u_min > u_max) continue;
        u384 l1_p1 = lo1 + 1;
        u384 u1_p1 = hi1 + 1;
        u384 l_eff = shl384(u_min, k1);
        if (l_eff > l1_p1) l1_p1 = l_eff;
        u384 u_eff = shl384(u_max, k1);
        if (u_eff < u1_p1) u1_p1 = u_eff;
        if (l1_p1 > u1_p1) continue;
        if (bit_length_fast(u1_p1) > 86) return -5;

        u128 l1_128 = (u128)l1_p1;
        u128 u1_128 = (u128)u1_p1;
        if (((u64)l1_128 & 1ULL) != 0ULL) l1_128 += 1;
        if (((u64)u1_128 & 1ULL) != 0ULL) u1_128 -= 1;
        if (l1_128 > u1_128) continue;
        u128 span128 = u1_128 - l1_128;
        int k_coll = bit_length_128(span128);
        if (k_coll < 1) k_coll = 1;
        if (k_coll > 80) return -5;
        ctx->l_eff = (u384)l1_128;
        ctx->u_eff = (u384)u1_128;
        ctx->u_eff_bl = bit_length_128(u1_128);

        u128 u_min_eff = (l1_128 + g_mask128[k1]) >> k1;
        if (((u64)u_min_eff & 1ULL) == 0ULL) u_min_eff += 1;
        u128 u_max_eff = u1_128 >> k1;
        if (u_max_eff < u_min_eff) continue;
        if (((u64)u_max_eff & 1ULL) == 0ULL) u_max_eff -= 1;
        if (u_min_eff > u_max_eff) continue;

        u64 rem_ulam_1 = ~0ULL;
        u64 req_lam_1 = 0ULL;
        u128 root_blo = b_lo_0;
        u128 root_bhi = b_hi_0;
        if (ulam_q126 > 0ULL) {
            if (ectx.tail_lb_q126[0] >= ulam_q126) continue;
            u64 max_root_tau = ulam_q126 - ectx.tail_lb_q126[0];
            if (l1_128 < u1_128 && step_term_lb_exact_q126((u384)(l1_128 - 1), k1) >= max_root_tau) {
                if (step_term_lb_exact_q126((u384)(u1_128 - 1), k1) >= max_root_tau) continue;
                u128 l_cert = l1_128;
                u128 bs_lo = l1_128 + 2;
                u128 bs_hi = u1_128 - 2;
                for (int it = 0; it < 20 && bs_lo <= bs_hi; it++) {
                    u128 mid = (bs_lo + ((bs_hi - bs_lo) >> 1)) & ~(u128)1;
                    if (mid < bs_lo) mid = bs_lo;
                    if (step_term_lb_exact_q126((u384)(mid - 1), k1) >= max_root_tau) {
                        l_cert = mid;
                        bs_lo = mid + 2;
                    } else {
                        if (mid < 4) break;
                        bs_hi = mid - 2;
                    }
                }
                l1_128 = l_cert + 2;
                if (l1_128 > u1_128) continue;
                span128 = u1_128 - l1_128;
                k_coll = bit_length_128(span128);
                if (k_coll < 1) k_coll = 1;
                ctx->l_eff = (u384)l1_128;
                u_min_eff = (l1_128 + g_mask128[k1]) >> k1;
                if (((u64)u_min_eff & 1ULL) == 0ULL) u_min_eff += 1;
                if (u_min_eff > u_max_eff) continue;
            }
            u64 root_lb = step_term_lb_exact_q126((u384)(u1_128 - 1), k1);
            if ((root_lb + ectx.tail_lb_q126[0]) >= ulam_q126) continue;
            rem_ulam_1 = ulam_q126 - root_lb;
            u128 p1 = pole_min_next_u128(rem_ulam_1 - ectx.tail_lb_q126[1]);
            if (p1 > b_hi_0) continue;
            if (p1 > root_blo) root_blo = p1;
            int skip_b = 0;
            for (int t = 1; t < exact_r; t++) {
                u64 avail_t = rem_ulam_1 - (ectx.tail_lb_q126[0] - ectx.step_lb_q126[t]);
                if (pole_min_next_u128(avail_t) > ectx.ceil_hi[t]) {
                    skip_b = 1;
                    break;
                }
            }
            if (skip_b) continue;
        }
        if (lam_lo_q126 > 0ULL) {
            u64 root_max_ub = step_term_ub_exact_q126((u384)(l1_128 - 1), k1);
            if ((root_max_ub + ectx.tail_ub_q126[0]) < lam_lo_q126) continue;
            if (l1_128 < u1_128 && (step_term_ub_exact_q126((u384)(u1_128 - 1), k1) + ectx.tail_ub_q126[0]) < lam_lo_q126) {
                u128 u_cert = u1_128;
                u128 bs_lo = l1_128 + 2;
                u128 bs_hi = u1_128 - 2;
                for (int it = 0; it < 20 && bs_lo <= bs_hi; it++) {
                    u128 mid = (bs_lo + ((bs_hi - bs_lo) >> 1)) & ~(u128)1;
                    if (mid < bs_lo) mid = bs_lo;
                    if ((step_term_ub_exact_q126((u384)(mid - 1), k1) + ectx.tail_ub_q126[0]) < lam_lo_q126) {
                        u_cert = mid;
                        if (mid < 4) break;
                        bs_hi = mid - 2;
                    } else {
                        bs_lo = mid + 2;
                    }
                }
                if (u_cert < 2) continue;
                u1_128 = u_cert - 2;
                if (l1_128 > u1_128) continue;
                span128 = u1_128 - l1_128;
                k_coll = bit_length_128(span128);
                if (k_coll < 1) k_coll = 1;
                ctx->u_eff = (u384)u1_128;
                ctx->u_eff_bl = bit_length_128(u1_128);
                u_max_eff = u1_128 >> k1;
                if (u_max_eff < u_min_eff) continue;
                if (((u64)u_max_eff & 1ULL) == 0ULL) u_max_eff -= 1;
                if (u_min_eff > u_max_eff) continue;
            }
            root_max_ub = step_term_ub_exact_q126((u384)(l1_128 - 1), k1);
            if ((root_max_ub + ectx.tail_ub_q126[0]) < lam_lo_q126) continue;
            req_lam_1 = (lam_lo_q126 > root_max_ub) ? (lam_lo_q126 - root_max_ub) : 0ULL;
            if (req_lam_1 > ectx.tail_ub_q126[1]) {
                u128 p_mx1 = pole_max_cur_u128(req_lam_1 - ectx.tail_ub_q126[1]);
                if (p_mx1 < root_blo) continue;
                if (p_mx1 < root_bhi) {
                    root_bhi = (((u64)p_mx1 & 1ULL) != 0ULL) ? p_mx1 : (p_mx1 - 1);
                }
            }
        }
        if (root_blo > root_bhi) continue;
        u128 n_odd_u1 = ((u_max_eff - u_min_eff) >> 1) + 1;
        if (n_odd_u1 <= (u128)4096) {
            u64 sub_c = 0ULL;
            for (u128 uc = u_min_eff; uc <= u_max_eff; uc += 2) {
                if ((sub_c & 15ULL) == 0ULL) {
                    ctx->leaf_ops++;
                    if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
                        ctx->aborted = 1;
                        break;
                    }
                }
                sub_c++;
                verify_z1_esc_u128(&ectx, (uc << k1) - 1);
                if (ctx->aborted) break;
            }
            if (ctx->aborted) break;
            continue;
        }
        if (k1 > 80) return -5;
        u128 p3_k1 = g_p3_128[k1];
        u256f ev_max = u256f_sub1(mul128_to_256f(p3_k1, u_max_eff));
        u128 two_root_blo = root_blo << 1;
        if (u256f_lt_u128(ev_max, two_root_blo)) continue;
        u256f ev_min = u256f_sub1(mul128_to_256f(p3_k1, u_min_eff));
        if (u256f_lt_u128(ev_min, two_root_blo)) {
            ev_min.lo = two_root_blo;
            ev_min.hi = 0;
        }

        int root_bhi_bl = (root_bhi == b_hi_0) ? b_hi_0_bl : bit_length_128(root_bhi);
        int ld_s = bit_length_256f(ev_min) - root_bhi_bl;
        if (ld_s < 1) ld_s = 1;
        if (u256f_gt_u128(u256f_shr(ev_min, ld_s), root_bhi)) ld_s += 1;
        int ld_e = bit_length_256f(ev_max) - bit_length_128(root_blo) + 1;
        if (ld_e < ld_s) continue;

        u256f z2_mx = u256f_shr(ev_max, ld_s);
        u256f z2_mn = u256f_shr(ev_min, ld_s);
        for (int l1 = ld_s; l1 <= ld_e; l1++, z2_mx = u256f_shr1(z2_mx), z2_mn = u256f_shr1(z2_mn)) {
            if (u256f_lt_u128(z2_mx, root_blo)) break;
            if (u256f_gt_u128(z2_mn, root_bhi)) continue;
            if (k1 + l1 >= k_coll) {
                u128 r128 = (((u128)1) << k1) * (u128)g_inv3[k1];
                test_cong_esc_u128(&ectx, r128 - l1_128, k1 + l1, l1_128, u1_128, span128);
                if (ctx->aborted) break;
                break;
            }
            u128 n_lo = u256f_le_u128(z2_mn, root_blo) ? root_blo : (z2_mn.lo | (u128)1);
            u128 n_hi = u256f_le_u128(z2_mx, root_bhi)
                ? ((((u64)z2_mx.lo & 1ULL) != 0ULL) ? z2_mx.lo : (z2_mx.lo - 1))
                : root_bhi;
            if (n_lo <= n_hi) {
                u256f g1 = {(((u128)1) << (k1 + l1)) - (((u128)1) << k1), (u128)0};
                int nxt1_fl_bl = (exact_r >= 2) ? bit_length_128(ectx.floor_lo[1]) : ctx->b_hi_bl;
                u128 s_cur = n_lo;
                for (int ci = 0; ci <= 13 && s_cur <= n_hi; ci++) {
                    u128 cut_hi = (ci < 13 && ((ectx.has_tight_win && req_lam_1 > 0ULL && s_cur < (((u128)1) << 82)) || esc_mid_bits[ci] < nxt1_fl_bl || esc_mid_bits[ci] <= 86))
                        ? ((((u128)1) << esc_mid_bits[ci]) - 1)
                        : n_hi;
                    u128 s_hi = (cut_hi < n_hi) ? cut_hi : n_hi;
                    if (s_hi < s_cur) continue;
                    dfs_std_esc_u128(&ectx, 1, k1 + l1, k1, g1, s_cur, s_hi, rem_ulam_1, req_lam_1, l1_128, u1_128, span128, k_coll);
                    if (ctx->aborted) break;
                    if (ci == 13 || s_hi >= n_hi) break;
                    s_cur = s_hi + 2;
                }
                if (ctx->aborted) break;
            }
        }
        if (ctx->aborted) break;
    }
    if (ctx->aborted == 0 && (ctx->nodes + ctx->leaf_ops) > ctx->max_budget) ctx->aborted = 1;
    *out_nodes = ctx->nodes;
    *out_leaf_ops = ctx->leaf_ops;
    *out_num_survivors = ctx->num_survivors;
    return ctx->aborted;
}

HENSEL_EXPORT int run_hensel_win_escalating_c(
    const u384_io *n0_io,
    const u384_io *w_lo_io,
    const u384_io *w_hi_io,
    const u384_io *b2_io,
    int exact_r,
    int max_survivors_cap,
    u64 ulam_q126,
    u64 lam_lo_q126,
    int num_bands,
    const BandIO *bands,
    const int *kd_lo,
    const int *kd_hi,
    u64 max_budget,
    u64 *out_nodes,
    u64 *out_leaf_ops,
    int *out_num_survivors,
    u384_io *out_survivors
) {
    ensure_stack_committed_win64();
    return run_hensel_win_escalating_impl(
        n0_io, w_lo_io, w_hi_io, b2_io, exact_r, max_survivors_cap, ulam_q126, lam_lo_q126,
        num_bands, bands, kd_lo, kd_hi, max_budget,
        out_nodes, out_leaf_ops, out_num_survivors, out_survivors
    );
}

HENSEL_EXPORT int run_hensel_std_escalating_c(
    const u384_io *n0_io,
    const u384_io *floors_io,
    const u384_io *b2_io,
    int exact_r,
    int max_survivors_cap,
    u64 ulam_q126,
    int num_bands,
    const BandIO *bands,
    const int *kd_lo,
    const int *kd_hi,
    u64 max_budget,
    u64 *out_nodes,
    u64 *out_leaf_ops,
    int *out_num_survivors,
    u384_io *out_survivors
) {
    ensure_stack_committed_win64();
    u384_io w_lo_adj[10];
    if (exact_r < 1 || exact_r > 8) return -6;
    for (int d = 0; d < exact_r; d++) {
        u384 fl_v = load_u384(&floors_io[d]);
        store_u384(&w_lo_adj[d], (fl_v + 1) | (u384)1);
    }
    return run_hensel_win_escalating_c(
        n0_io, w_lo_adj, 0, b2_io, exact_r, max_survivors_cap, ulam_q126, 0ULL,
        num_bands, bands, kd_lo, kd_hi, max_budget,
        out_nodes, out_leaf_ops, out_num_survivors, out_survivors
    );
}

// ============================================================================
// Heterogeneous CPU-Frontier + OpenCL-GPU Subtree Exports (Bit-Exact Q126)
// ============================================================================

typedef struct {
    u64 g_lo_0, g_lo_1, g_hi_0, g_hi_1;
    u64 lo_z_0, lo_z_1;
    u64 hi_z_0, hi_z_1;
    u64 l1_0, l1_1;
    u64 u1_0, u1_1;
    u64 rem_ulam;
    u64 req_lam_lo;
    int depth;
    int k_exp;
    int w_exp;
    int k_coll;
} GpuHenselTask;

typedef struct {
    u64 b_hi_0, b_hi_1;
    u64 two_b_hi_0, two_b_hi_1;
    u64 floor_lo[10][2];
    u64 ceil_hi[10][2];
    u64 step_lb_q126[11];
    u64 tail_ub_q126[11];
    u64 tail_lb_q126[11];
    int ceil_hi_bl[10];
    int min_ceil_idx[11];
    int kd_lo[160];
    int kd_hi[160];
    int exact_r;
    int kd_lo_monotone;
    int has_tight_win;
    int b_hi_bl;
    int pad_end;
} GpuEscBoxParams;

typedef struct {
    u64 p3_128[81][2];
    u64 max_u_128[81][2];
    u64 inv3_128[256][2];
    u64 recip3_lb[81][2];
    u64 recip3_ub[81][2];
    u64 num23_ub_q62[256];
    u64 num23_lb_q62[256];
    int p3_bl[195];
    int kd_jump[140];
    int pad_tbl;
} GpuQ126ConstTables;

HENSEL_EXPORT void export_q126_gpu_tables_c(
    GpuQ126ConstTables *out_const,
    u64 *out_inv_z_ub,
    u64 *out_inv_zp1_lb
) {
    ensure_q126_tables();
    for (int k = 0; k <= 80; k++) {
        out_const->p3_128[k][0] = (u64)g_p3_128[k];
        out_const->p3_128[k][1] = (u64)(g_p3_128[k] >> 64);
        out_const->max_u_128[k][0] = (u64)g_max_u_128[k];
        out_const->max_u_128[k][1] = (u64)(g_max_u_128[k] >> 64);
        out_const->recip3_lb[k][0] = (u64)g_recip3_lb[k];
        out_const->recip3_lb[k][1] = (u64)(g_recip3_lb[k] >> 64);
        out_const->recip3_ub[k][0] = (u64)g_recip3_ub[k];
        out_const->recip3_ub[k][1] = (u64)(g_recip3_ub[k] >> 64);
    }
    for (int k = 0; k < 256; k++) {
        u128 iv = (u128)g_inv3[k];
        out_const->inv3_128[k][0] = (u64)iv;
        out_const->inv3_128[k][1] = (u64)(iv >> 64);
        out_const->num23_ub_q62[k] = g_num23_ub_q62[k];
        out_const->num23_lb_q62[k] = g_num23_lb_q62[k];
    }
    for (int k = 0; k < 195; k++) out_const->p3_bl[k] = g_p3_bl[k];
    for (int d = 0; d < 140; d++) out_const->kd_jump[d] = g_kd_jump[d];
    out_const->pad_tbl = 0;
    for (int b = 0; b < 130; b++) {
        for (int top = 0; top < 2048; top++) {
            out_inv_z_ub[b * 2048 + top] = g_inv_z_ub_tbl[b][top];
            out_inv_zp1_lb[b * 2048 + top] = g_inv_zp1_lb_tbl[b][top];
        }
    }
}

typedef struct {
    EscStdCtx ectx;
    int split_depth;
    int max_tasks;
    int num_tasks;
    int tasks_overflowed;
    GpuHenselTask *out_tasks;
} GpuFrontierCtx;

static void dfs_collect_gpu_esc_u128(
    GpuFrontierCtx *fctx,
    int depth,
    int k_exp,
    int w_exp,
    u256f g_val,
    u128 lo_z,
    u128 hi_z,
    u64 rem_ulam,
    u64 req_lam_lo,
    u128 l1_128,
    u128 u1_128,
    u128 span128,
    int k_coll
) {
    EscStdCtx *ectx = &fctx->ectx;
    HenselCtx *ctx = &ectx->base;
    if (ctx->aborted) return;

    if (depth >= fctx->split_depth && w_exp <= 80 && k_exp + 1 < k_coll && fctx->num_tasks < fctx->max_tasks) {
        int need_cpu_sh = (
            depth == 1
            || (
                depth == 2
                && depth < ectx->exact_r
                && ectx->lam_lo_q126 > 0ULL
                && ectx->floor_lo[1] < (((u128)1) << 82)
                && k_exp <= 126
                && (k_coll - k_exp) >= 8
            )
        );
        if (!need_cpu_sh) {
            GpuHenselTask *t = &fctx->out_tasks[fctx->num_tasks++];
            t->g_lo_0 = (u64)g_val.lo;
            t->g_lo_1 = (u64)(g_val.lo >> 64);
            t->g_hi_0 = (u64)g_val.hi;
            t->g_hi_1 = (u64)(g_val.hi >> 64);
            t->lo_z_0 = (u64)lo_z;
            t->lo_z_1 = (u64)(lo_z >> 64);
            t->hi_z_0 = (u64)hi_z;
            t->hi_z_1 = (u64)(hi_z >> 64);
            t->l1_0 = (u64)l1_128;
            t->l1_1 = (u64)(l1_128 >> 64);
            t->u1_0 = (u64)u1_128;
            t->u1_1 = (u64)(u1_128 >> 64);
            t->rem_ulam = rem_ulam;
            t->req_lam_lo = req_lam_lo;
            t->depth = depth;
            t->k_exp = k_exp;
            t->w_exp = w_exp;
            t->k_coll = k_coll;
            return;
        }
    }

    ctx->nodes++;
    if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
        ctx->aborted = 1;
        return;
    }
    if (k_exp + 1 >= k_coll) {
        u128 r128 = ((u128)0 - g_val.lo) * (u128)g_inv3[w_exp];
        test_cong_esc_u128(ectx, r128 - l1_128, k_exp + 1, l1_128, u1_128, span128);
        return;
    }

    u128 hi_p1 = hi_z + 1;
    u128 lo_p1 = lo_z + 1;
    int ex_r = ectx->exact_r;
    if (req_lam_lo > ectx->tail_ub_q126[depth]) {
        u64 deficit_cur = req_lam_lo - ectx->tail_ub_q126[depth];
        u64 max_ub_cur = (lo_p1 > (((u128)1) << 84))
            ? inv_z_ub_fast_q126((u384)(lo_p1 - 1))
            : inv_z_ub_exact_q126((u384)(lo_p1 - 1));
        if (max_ub_cur < deficit_cur) return;
        u128 max_zp1 = pole_max_cur_u128(deficit_cur) + (u128)1;
        if (max_zp1 < lo_p1) return;
        if (max_zp1 < hi_p1) {
            hi_p1 = max_zp1 & ~(u128)1;
            if (hi_p1 < lo_p1) return;
        }
    }
    if (w_exp <= 80 && ctx->u_eff_bl <= 86 && ((g_val.hi >> 122) == 0)) {
        u128 p3w = g_p3_128[w_exp];
        int shrank = 0;
        u256f z_aff_hi = u256f_shr(u256f_add(mul128_to_256f(p3w, u1_128), g_val), k_exp);
        if (u256f_lt_u128(z_aff_hi, lo_p1)) return;
        if (u256f_lt_u128(z_aff_hi, hi_p1)) {
            u128 zh = z_aff_hi.lo;
            if (((u64)zh & 1ULL) != 0ULL) zh -= 1;
            if (zh < lo_p1) return;
            hi_p1 = zh;
        } else if (u256f_gt_u128(z_aff_hi, hi_p1) && k_exp < 126) {
            u256f h_prod = u256f_shl_u128(hi_p1, k_exp);
            if (!u256f_gt(h_prod, g_val)) return;
            u256f x_hi = u256f_sub(h_prod, g_val);
            int xbl = bit_length_256f(x_hi);
            int s_sh = (xbl > 126) ? (xbl - 126) : 0;
            int r_sh = 126 + g_p3_bl[w_exp] - s_sh;
            if (r_sh > 0) {
                u256f u_cand = u256f_shr(mul128_to_256f(u256f_shr(x_hi, s_sh).lo + 1, g_recip3_ub[w_exp]), r_sh);
                if (u256f_lt_u128(u_cand, u1_128)) {
                    u128 u_n = u_cand.lo;
                    if (((u64)u_n & 1ULL) != 0ULL) u_n -= 1;
                    if (u_n < l1_128) return;
                    u1_128 = u_n;
                    shrank = 1;
                }
            }
        }
        u128 m128 = g_mask128[k_exp];
        u256f z_aff_lo = u256f_shr(u256f_add_u128(u256f_add(mul128_to_256f(p3w, l1_128), g_val), m128), k_exp);
        if (u256f_gt_u128(z_aff_lo, hi_p1)) return;
        if (u256f_gt_u128(z_aff_lo, lo_p1)) {
            u128 zl = z_aff_lo.lo;
            if (((u64)zl & 1ULL) != 0ULL) zl += 1;
            if (zl > hi_p1) return;
            lo_p1 = zl;
        } else if (u256f_lt_u128(z_aff_lo, lo_p1) && k_exp < 126) {
            u256f l_prod = u256f_shl_u128(lo_p1, k_exp);
            if (u256f_gt(l_prod, g_val)) {
                u256f x_lo = u256f_sub(l_prod, g_val);
                int xbl = bit_length_256f(x_lo);
                int s_sh = (xbl > 126) ? (xbl - 126) : 0;
                int r_sh = 126 + g_p3_bl[w_exp] - s_sh;
                if (r_sh > 0) {
                    u256f l_cand = u256f_shr(mul128_to_256f(u256f_shr(x_lo, s_sh).lo, g_recip3_lb[w_exp]), r_sh);
                    if (u256f_gt_u128(l_cand, u1_128)) return;
                    if (l_cand.lo > l1_128) {
                        u128 l_n = l_cand.lo;
                        if (((u64)l_n & 1ULL) != 0ULL) l_n += 1;
                        if (l_n > u1_128) return;
                        l1_128 = l_n;
                        shrank = 1;
                    }
                }
            }
        }
        if (shrank) {
            span128 = u1_128 - l1_128;
            k_coll = bit_length_128(span128);
            if (k_coll < 1) k_coll = 1;
            if (k_exp + 1 >= k_coll) {
                u128 r128 = ((u128)0 - g_val.lo) * (u128)g_inv3[w_exp];
                test_cong_esc_u128(ectx, r128 - l1_128, k_exp + 1, l1_128, u1_128, span128);
                return;
            }
        }
    }

    u128 cur_hi = (((u64)(hi_p1 - 1) & 1ULL) != 0ULL) ? (hi_p1 - 1) : (hi_p1 - 2);
    if (rem_ulam != ~0ULL && step_term_lb_u128(cur_hi, 1) >= rem_ulam) return;

    int b_hi_cur = bit_length_128(hi_p1);
    u128 b_hi_128 = (u128)ctx->b_hi;
    u128 two_b_hi_128 = (u128)ctx->two_b_hi;

    if (depth == ex_r) {
        int kd_start = ctx->kd_hi[b_hi_cur];
        if (kd_start >= b_hi_cur) return;
        if (ectx->ulam_hi_q126 > 0ULL && (k_coll - k_exp) >= 6 && depth <= 2) {
            int sh_rc = shrink_band_coupled_q126(ectx, depth, k_exp, w_exp, g_val, kd_start, &l1_128, &u1_128);
            if (sh_rc == 0) return;
            if (sh_rc == 2) {
                span128 = u1_128 - l1_128;
                k_coll = bit_length_128(span128);
                if (k_coll < 1) k_coll = 1;
                if (k_exp + 1 >= k_coll) {
                    u128 r128 = ((u128)0 - g_val.lo) * (u128)g_inv3[w_exp];
                    test_cong_esc_u128(ectx, r128 - l1_128, k_exp + 1, l1_128, u1_128, span128);
                    return;
                }
            }
        }
        if (k_exp + kd_start + 5 >= k_coll && w_exp <= 80) {
            u128 rc_e = ((u128)0 - g_val.lo) * (u128)g_inv3[w_exp];
            test_cong_from_depth_esc_u128(ectx, depth, k_exp, w_exp, g_val, lo_p1, hi_p1, rc_e - l1_128, k_exp + kd_start, l1_128, u1_128, span128);
            return;
        }
        u128 p3k_g128 = (kd_start <= 80) ? (g_p3_128[kd_start] * g_val.lo) : (u128)0;
        for (int kd = kd_start; kd < b_hi_cur; kd++) {
            ctx->leaf_ops++;
            if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
                ctx->aborted = 1;
                return;
            }
            if (rem_ulam != ~0ULL && step_term_lb_u128(cur_hi, kd) >= rem_ulam) break;
            int s_kkd = k_exp + kd;
            if (s_kkd >= k_coll) {
                u128 rc = ((u128)0 - g_val.lo) * (u128)g_inv3[w_exp];
                test_cong_esc_u128(ectx, rc - l1_128, s_kkd, l1_128, u1_128, span128);
                return;
            }
            if (s_kkd + 5 >= k_coll && w_exp <= 80) {
                u128 rc = ((u128)0 - g_val.lo) * (u128)g_inv3[w_exp];
                test_cong_from_depth_esc_u128(ectx, depth, k_exp, w_exp, g_val, lo_p1, hi_p1, rc - l1_128, s_kkd, l1_128, u1_128, span128);
                return;
            }
            u128 cur_p3g = p3k_g128;
            p3k_g128 += (p3k_g128 << 1);
            if (req_lam_lo > 0ULL) {
                u64 lf_ub = (lo_p1 > (((u128)1) << 84))
                    ? step_term_ub_fast_q126((u384)(lo_p1 - 1), kd)
                    : step_term_ub_exact_q126((u384)(lo_p1 - 1), kd);
                if (lf_ub < req_lam_lo) continue;
            }
            u128 u_max = hi_p1 >> kd;
            if (u_max == 0) continue;
            if (((u64)u_max & 1ULL) == 0ULL) u_max -= 1;
            if (u_max < 1) continue;
            u128 u_min_l = (lo_p1 + g_mask128[kd]) >> kd;
            if (u_min_l > u_max) continue;
            u256f ev_max = u256f_sub1(mul128_to_256f(g_p3_128[kd], u_max));
            if (u256f_le_u128(ev_max, two_b_hi_128)) continue;
            u128 inv_wn = (u128)g_inv3[w_exp + kd];
            u128 bd128 = (((((u128)1) << s_kkd) - cur_p3g) * inv_wn) - l1_128;
            u128 inv_sh = inv_wn << (s_kkd + 1);
            int ld_lim = bit_length_256f(ev_max) - ctx->b_hi_bl + 2;
            u256f z_ev = u256f_shr1(ev_max);
            for (int ld = 1; ld <= ld_lim; ld++, z_ev = u256f_shr1(z_ev)) {
                if (u256f_le_u128(z_ev, b_hi_128)) break;
                int k_n = s_kkd + ld;
                if (k_n >= k_coll) {
                    test_cong_esc_u128(ectx, bd128, k_n, l1_128, u1_128, span128);
                    break;
                }
                test_cong_esc_u128(ectx, bd128 - inv_sh, k_n + 1, l1_128, u1_128, span128);
                inv_sh <<= 1;
                if (ctx->aborted) return;
            }
        }
        return;
    }

    u128 base_nxt_lo = ectx->floor_lo[depth];
    u128 step_b_hi = ectx->ceil_hi[depth];
    int step_b_hi_bl = ectx->ceil_hi_bl[depth];
    int next_is_leaf = (depth + 1 == ex_r);
    int t_star = ectx->min_ceil_idx[depth];
    int kd_start = min_kd_for_jump(b_hi_cur, bit_length_128(base_nxt_lo));
    if (ectx->kd_lo_monotone && ctx->kd_lo != 0 && ctx->kd_lo[b_hi_cur] > kd_start) kd_start = ctx->kd_lo[b_hi_cur];
    if (kd_start >= b_hi_cur) return;
    if (rem_ulam != ~0ULL) {
        u64 lb0 = step_term_lb_u128(cur_hi, kd_start);
        if ((lb0 + ectx->tail_lb_q126[depth]) >= rem_ulam) return;
        u64 max_nxt_rem = rem_ulam - lb0;
        u128 p_nxt0 = pole_min_next_u128(max_nxt_rem - ectx->tail_lb_q126[depth + 1]);
        if (p_nxt0 > step_b_hi) return;
        if (t_star != depth) {
            u64 avail_ts0 = max_nxt_rem - (ectx->tail_lb_q126[depth] - ectx->step_lb_q126[t_star]);
            if (pole_min_next_u128(avail_ts0) > ectx->ceil_hi[t_star]) return;
        }
        if (p_nxt0 > base_nxt_lo) {
            base_nxt_lo = p_nxt0;
            int kd2 = min_kd_for_jump(b_hi_cur, bit_length_128(base_nxt_lo));
            if (kd2 > kd_start) {
                kd_start = kd2;
                if (kd_start >= b_hi_cur) return;
                u64 lb2 = step_term_lb_u128(cur_hi, kd_start);
                if ((lb2 + ectx->tail_lb_q126[depth]) >= rem_ulam) return;
            }
        }
    }
    int run_sh = ((ectx->lam_lo_q126 > 0ULL && depth <= 2 && ectx->floor_lo[depth - 1] < (((u128)1) << 82))
            || (ectx->ulam_hi_q126 > 0ULL && (depth == 1 || lo_p1 <= (((u128)1) << 85))))
        && (k_coll - k_exp) >= 6
        && (depth == 1
            || (depth == 2 && w_exp <= 80 && k_exp <= 126 && (k_coll - k_exp) >= 8)
            || (depth == 3 && w_exp <= 80 && k_exp <= 126 && (k_coll - k_exp) >= 14));
    if (run_sh) {
        int sh_rc = shrink_band_coupled_q126(ectx, depth, k_exp, w_exp, g_val, kd_start, &l1_128, &u1_128);
        if (sh_rc == 0) return;
        if (sh_rc == 2) {
            span128 = u1_128 - l1_128;
            k_coll = bit_length_128(span128);
            if (k_coll < 1) k_coll = 1;
            if (k_exp + 1 >= k_coll) {
                u128 r128 = ((u128)0 - g_val.lo) * (u128)g_inv3[w_exp];
                test_cong_esc_u128(ectx, r128 - l1_128, k_exp + 1, l1_128, u1_128, span128);
                return;
            }
            if (w_exp <= 80 && k_exp <= 80) {
                u128 p3w = g_p3_128[w_exp];
                u256f z_aff_hi = u256f_shr(u256f_add(mul128_to_256f(p3w, u1_128), g_val), k_exp);
                if (u256f_lt_u128(z_aff_hi, lo_p1)) return;
                if (u256f_lt_u128(z_aff_hi, hi_p1)) {
                    u128 zh = z_aff_hi.lo;
                    if (((u64)zh & 1ULL) != 0ULL) zh -= 1;
                    if (zh < lo_p1) return;
                    hi_p1 = zh;
                }
                u256f z_aff_lo = u256f_shr(u256f_add_u128(u256f_add(mul128_to_256f(p3w, l1_128), g_val), g_mask128[k_exp]), k_exp);
                if (u256f_gt_u128(z_aff_lo, hi_p1)) return;
                if (u256f_gt_u128(z_aff_lo, lo_p1)) {
                    u128 zl = z_aff_lo.lo;
                    if (((u64)zl & 1ULL) != 0ULL) zl += 1;
                    if (zl > hi_p1) return;
                    lo_p1 = zl;
                }
                cur_hi = (((u64)(hi_p1 - 1) & 1ULL) != 0ULL) ? (hi_p1 - 1) : (hi_p1 - 2);
                b_hi_cur = bit_length_128(hi_p1);
                kd_start = min_kd_for_jump(b_hi_cur, bit_length_128(base_nxt_lo));
                if (ectx->kd_lo_monotone && ctx->kd_lo != 0 && ctx->kd_lo[b_hi_cur] > kd_start) kd_start = ctx->kd_lo[b_hi_cur];
                if (kd_start >= b_hi_cur) return;
            }
        }
    }
    if (rem_ulam != ~0ULL && (step_term_lb_u128(cur_hi, kd_start) + ectx->tail_lb_q126[depth]) >= rem_ulam) return;
    int e_gap = next_is_leaf ? 4 : 3;
    if (k_exp + kd_start + e_gap >= k_coll && w_exp < 350) {
        u128 rc_e = ((u128)0 - g_val.lo) * (u128)g_inv3[w_exp];
        if (w_exp <= 80) {
            test_cong_from_depth_esc_u128(ectx, depth, k_exp, w_exp, g_val, lo_p1, hi_p1, rc_e - l1_128, k_exp + kd_start, l1_128, u1_128, span128);
        } else {
            test_cong_esc_u128(ectx, rc_e - l1_128, k_exp + kd_start, l1_128, u1_128, span128);
        }
        return;
    }
    u128 p3k_g_lo = (kd_start <= 80) ? (g_p3_128[kd_start] * g_val.lo) : (u128)0;

    for (int kd = kd_start; kd < b_hi_cur; kd++) {
        if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
            ctx->aborted = 1;
            return;
        }
        u64 nxt_rem = rem_ulam;
        if (rem_ulam != ~0ULL) {
            u64 cur_lb = step_term_lb_u128(cur_hi, kd);
            if ((cur_lb + ectx->tail_lb_q126[depth]) >= rem_ulam) break;
            nxt_rem = rem_ulam - cur_lb;
        }
        int s_kkd = k_exp + kd;
        if (s_kkd >= k_coll) {
            u128 rc = ((u128)0 - g_val.lo) * (u128)g_inv3[w_exp];
            test_cong_esc_u128(ectx, rc - l1_128, s_kkd, l1_128, u1_128, span128);
            break;
        }
        u128 eff_b_lo = base_nxt_lo;
        if (rem_ulam != ~0ULL) {
            u128 p_nxt = pole_min_next_u128(nxt_rem - ectx->tail_lb_q126[depth + 1]);
            if (p_nxt > step_b_hi) break;
            if (p_nxt > eff_b_lo) eff_b_lo = p_nxt;
            if (t_star != depth) {
                u64 avail_ts = nxt_rem - (ectx->tail_lb_q126[depth] - ectx->step_lb_q126[t_star]);
                if (pole_min_next_u128(avail_ts) > ectx->ceil_hi[t_star]) break;
            }
        }
        if (eff_b_lo > step_b_hi) break;
        if (eff_b_lo > base_nxt_lo && kd < min_kd_for_jump(b_hi_cur, bit_length_128(eff_b_lo))) {
            p3k_g_lo += (p3k_g_lo << 1);
            continue;
        }
        if (s_kkd + e_gap >= k_coll && w_exp <= 80) {
            u128 rc = ((u128)0 - g_val.lo) * (u128)g_inv3[w_exp];
            test_cong_from_depth_esc_u128(ectx, depth, k_exp, w_exp, g_val, lo_p1, hi_p1, rc - l1_128, s_kkd, l1_128, u1_128, span128);
            break;
        }
        u128 cur_p3g_lo = p3k_g_lo;
        p3k_g_lo += (p3k_g_lo << 1);

        u128 u_min = (lo_p1 + g_mask128[kd]) >> kd;
        if (u_min < 1) u_min = 1;
        if (((u64)u_min & 1ULL) == 0ULL) u_min += 1;
        u128 u_max = hi_p1 >> kd;
        if (u_max < u_min) continue;
        if (((u64)u_max & 1ULL) == 0ULL) u_max -= 1;
        if (u_min > u_max) continue;

        u128 p3_kd = g_p3_128[kd];
        u256f ev_max = u256f_sub1(mul128_to_256f(p3_kd, u_max));
        u128 two_eff_blo = eff_b_lo << 1;
        if (u256f_lt_u128(ev_max, two_eff_blo)) continue;
        u256f ev_min = u256f_sub1(mul128_to_256f(p3_kd, u_min));
        u128 kd_lo_p1 = lo_p1;
        if (u256f_lt_u128(ev_min, two_eff_blo)) {
            if (kd <= 80) {
                u128 u_lb = u256f_shr(mul128_to_256f(two_eff_blo, g_recip3_lb[kd]), 126 + g_p3_bl[kd]).lo + (u128)1;
                if (((u64)u_lb & 1ULL) == 0ULL) u_lb += (u128)1;
                if (u_lb > u_min) {
                    if (u_lb > u_max) continue;
                    u_min = u_lb;
                    u128 cand_lo_p1 = u_min << kd;
                    if (cand_lo_p1 > kd_lo_p1) kd_lo_p1 = cand_lo_p1;
                }
            }
            ev_min.lo = two_eff_blo;
            ev_min.hi = 0;
        }

        u64 nxt_req_lam = 0ULL;
        u128 eff_b_hi = step_b_hi;
        int eff_b_hi_bl = step_b_hi_bl;
        if (req_lam_lo > 0ULL) {
            u64 cur_ub = (kd_lo_p1 > (((u128)1) << 84))
                ? step_term_ub_fast_q126((u384)(kd_lo_p1 - 1), kd)
                : step_term_ub_exact_q126((u384)(kd_lo_p1 - 1), kd);
            if ((cur_ub + ectx->tail_ub_q126[depth]) < req_lam_lo) continue;
            nxt_req_lam = (req_lam_lo > cur_ub) ? (req_lam_lo - cur_ub) : 0ULL;
            if (nxt_req_lam > ectx->tail_ub_q126[depth + 1]) {
                u128 p_mx = pole_max_cur_u128(nxt_req_lam - ectx->tail_ub_q126[depth + 1]);
                if (p_mx < eff_b_lo) continue;
                if (p_mx < eff_b_hi) {
                    eff_b_hi = (((u64)p_mx & 1ULL) != 0ULL) ? p_mx : (p_mx - 1);
                    if (eff_b_lo > eff_b_hi) continue;
                    eff_b_hi_bl = bit_length_128(eff_b_hi);
                }
            }
        }
        int ld_start = bit_length_256f(ev_min) - eff_b_hi_bl;
        if (ld_start < 1) ld_start = 1;
        if (u256f_gt_u128(u256f_shr(ev_min, ld_start), eff_b_hi)) ld_start += 1;
        int ld_end = bit_length_256f(ev_max) - bit_length_128(eff_b_lo) + 1;
        if (ld_start > ld_end) continue;
        u256f z_mx = u256f_shr(ev_max, ld_start);
        if (u256f_lt_u128(z_mx, eff_b_lo)) continue;

        int w_n = w_exp + kd;
        u128 inv_wn = (u128)g_inv3[w_n];
        u128 sh_kkd_128 = ((u128)1) << s_kkd;
        u128 base_diff_128 = ((sh_kkd_128 - cur_p3g_lo) * inv_wn) - l1_128;
        int have_p3g = 0;
        u256f p3k_g_full = {(u128)0, (u128)0};

        if (next_is_leaf) {
            u256f z_mn = u256f_shr(ev_min, ld_start);
            for (int ld = ld_start; ld <= ld_end; ld++, z_mx = u256f_shr1(z_mx), z_mn = u256f_shr1(z_mn)) {
                if (u256f_lt_u128(z_mx, eff_b_lo)) break;
                if (u256f_gt_u128(z_mn, eff_b_hi)) continue;
                int k_n = s_kkd + ld;
                if (k_n >= k_coll) {
                    test_cong_esc_u128(ectx, base_diff_128, k_n, l1_128, u1_128, span128);
                    break;
                }
                u128 cur_inv = inv_wn << k_n;
                u128 n_hi = u256f_le_u128(z_mx, eff_b_hi)
                    ? ((((u64)z_mx.lo & 1ULL) != 0ULL) ? z_mx.lo : (z_mx.lo - 1))
                    : eff_b_hi;
                u128 n_lo = u256f_le_u128(z_mn, eff_b_lo) ? eff_b_lo : (z_mn.lo | (u128)1);
                if (n_lo > n_hi) continue;
                int b_nhi = bit_length_128(n_hi + 1);
                int ks = ctx->kd_hi[b_nhi];
                if (ks >= b_nhi) continue;
                int s_exp = k_n + ks;
                if (s_exp >= k_coll) {
                    test_cong_esc_u128(ectx, base_diff_128 - cur_inv, s_exp, l1_128, u1_128, span128);
                } else {
                    int b_nlo = bit_length_128(n_lo + 1);
                    int ks_max_lf = ctx->kd_hi[b_nlo];
                    if ((((!ectx->has_tight_win || nxt_req_lam == 0ULL || b_nlo >= 82) && b_nlo >= 80)
                            || ((b_nhi - b_nlo <= 2) && (nxt_req_lam == 0ULL || b_nlo >= 80)))
                        && (k_n + ks_max_lf) < k_coll
                        && (nxt_rem == ~0ULL || step_term_lb_u128(n_lo, ks_max_lf) < nxt_rem)) {
                        if (!have_p3g) {
                            p3k_g_full = u256f_mul_u128(g_val, p3_kd);
                            have_p3g = 1;
                        }
                        u256f g_n = u256f_add_u128(p3k_g_full, (((u128)1) << k_n) - sh_kkd_128);
                        ectx->step_kd[depth] = kd;
                        ectx->step_k_exp[depth] = k_exp;
                        ectx->step_w_exp[depth] = w_exp;
                        ectx->step_g_val[depth] = g_val;
                        dfs_collect_gpu_esc_u128(fctx, depth + 1, k_n, w_n, g_n, n_lo, n_hi, nxt_rem, nxt_req_lam, l1_128, u1_128, span128, k_coll);
                        if (ctx->aborted) return;
                    } else {
                        int min_s_coll = 1000;
                        int have_gn_lf = 0;
                        u256f g_n = {(u128)0, (u128)0};
                        u128 s_cur = n_lo;
                        for (int ci = 0; ci <= 12 && s_cur <= n_hi; ci++) {
                            u128 cut_hi = (ci < 12) ? ((((u128)1) << esc_leaf_bits[ci]) - 1) : n_hi;
                            u128 s_hi = (cut_hi < n_hi) ? cut_hi : n_hi;
                            if (s_hi < s_cur) continue;
                            int b_shi = bit_length_128(s_hi + 1);
                            int ks_sub = ctx->kd_hi[b_shi];
                            if (ks_sub < b_shi) {
                                int se_sub = k_n + ks_sub;
                                if (se_sub >= k_coll) {
                                    if (se_sub < min_s_coll) min_s_coll = se_sub;
                                } else {
                                    if ((!ectx->has_tight_win || nxt_req_lam == 0ULL || s_cur >= (((u128)1) << 82))
                                        && s_cur >= (((u128)1) << 80)) {
                                        s_hi = n_hi;
                                        b_shi = bit_length_128(s_hi + 1);
                                        ks_sub = ctx->kd_hi[b_shi];
                                    }
                                    if (ks_sub < b_shi && (nxt_rem == ~0ULL || step_term_lb_u128(s_hi, ks_sub) < nxt_rem)) {
                                        if (!have_gn_lf) {
                                            if (!have_p3g) {
                                                p3k_g_full = u256f_mul_u128(g_val, p3_kd);
                                                have_p3g = 1;
                                            }
                                            g_n = u256f_add_u128(p3k_g_full, (((u128)1) << k_n) - sh_kkd_128);
                                            have_gn_lf = 1;
                                        }
                                        ectx->step_kd[depth] = kd;
                                        ectx->step_k_exp[depth] = k_exp;
                                        ectx->step_w_exp[depth] = w_exp;
                                        ectx->step_g_val[depth] = g_val;
                                        dfs_collect_gpu_esc_u128(fctx, depth + 1, k_n, w_n, g_n, s_cur, s_hi, nxt_rem, nxt_req_lam, l1_128, u1_128, span128, k_coll);
                                        if (ctx->aborted) return;
                                    }
                                }
                            }
                            if (ci == 12 || s_hi >= n_hi) break;
                            s_cur = s_hi + 2;
                        }
                        if (min_s_coll < 1000) {
                            test_cong_esc_u128(ectx, base_diff_128 - cur_inv, min_s_coll, l1_128, u1_128, span128);
                            if (ctx->aborted) return;
                        }
                    }
                }
            }
        } else {
            u256f z_mn = u256f_shr(ev_min, ld_start);
            int nxt2_fl_bl = bit_length_128(ectx->floor_lo[depth + 1]);
            for (int ld = ld_start; ld <= ld_end; ld++, z_mx = u256f_shr1(z_mx), z_mn = u256f_shr1(z_mn)) {
                if (u256f_lt_u128(z_mx, eff_b_lo)) break;
                if (u256f_gt_u128(z_mn, eff_b_hi)) continue;
                int k_n = s_kkd + ld;
                if (k_n >= k_coll) {
                    test_cong_esc_u128(ectx, base_diff_128, k_n, l1_128, u1_128, span128);
                    break;
                }
                u128 n_hi = u256f_le_u128(z_mx, eff_b_hi)
                    ? ((((u64)z_mx.lo & 1ULL) != 0ULL) ? z_mx.lo : (z_mx.lo - 1))
                    : eff_b_hi;
                u128 n_lo = u256f_le_u128(z_mn, eff_b_lo) ? eff_b_lo : (z_mn.lo | (u128)1);
                if (n_lo <= n_hi) {
                    int b_nhi_nxt = bit_length_128(n_hi + 1);
                    int ks_nxt = min_kd_for_jump(b_nhi_nxt, nxt2_fl_bl);
                    if (ectx->kd_lo_monotone && ctx->kd_lo != 0 && ctx->kd_lo[b_nhi_nxt] > ks_nxt) ks_nxt = ctx->kd_lo[b_nhi_nxt];
                    if (ks_nxt >= b_nhi_nxt) continue;
                    int s_exp_nxt = k_n + ks_nxt;
                    if (s_exp_nxt >= k_coll) {
                        test_cong_esc_u128(ectx, base_diff_128 - (inv_wn << k_n), s_exp_nxt, l1_128, u1_128, span128);
                        if (ctx->aborted) return;
                    } else {
                        if (nxt_rem != ~0ULL && (step_term_lb_u128(n_hi, ks_nxt) + ectx->tail_lb_q126[depth + 1]) >= nxt_rem) continue;
                        int b_nlo_m = bit_length_128(n_lo + 1);
                        int ks_max_m = min_kd_for_jump(b_nlo_m, nxt2_fl_bl);
                        if (ectx->kd_lo_monotone && ctx->kd_lo != 0 && ctx->kd_lo[b_nlo_m] > ks_max_m) ks_max_m = ctx->kd_lo[b_nlo_m];
                        if ((((!ectx->has_tight_win || nxt_req_lam == 0ULL || b_nlo_m >= 82) && b_nlo_m >= (depth >= 2 ? 80 : 82))
                                || ((b_nhi_nxt - b_nlo_m <= (b_nlo_m < 84 ? 1 : 2)) && (nxt_req_lam == 0ULL || b_nlo_m >= 80)))
                            && (k_n + ks_max_m) < k_coll
                            && (nxt_rem == ~0ULL || (step_term_lb_u128(n_lo, ks_max_m) + ectx->tail_lb_q126[depth + 1]) < nxt_rem)) {
                            if (!have_p3g) {
                                p3k_g_full = u256f_mul_u128(g_val, p3_kd);
                                have_p3g = 1;
                            }
                            u256f g_n = u256f_add_u128(p3k_g_full, (((u128)1) << k_n) - sh_kkd_128);
                            ectx->step_kd[depth] = kd;
                            ectx->step_k_exp[depth] = k_exp;
                            ectx->step_w_exp[depth] = w_exp;
                            ectx->step_g_val[depth] = g_val;
                            dfs_collect_gpu_esc_u128(fctx, depth + 1, k_n, w_n, g_n, n_lo, n_hi, nxt_rem, nxt_req_lam, l1_128, u1_128, span128, k_coll);
                            if (ctx->aborted) return;
                        } else {
                            int min_s_coll = 1000;
                            int have_gn_nl = 0;
                            u256f g_n = {(u128)0, (u128)0};
                            u128 s_cur = n_lo;
                            for (int ci = 0; ci <= 13 && s_cur <= n_hi; ci++) {
                                u128 cut_hi = (ci < 13 && ((ectx->has_tight_win && nxt_req_lam > 0ULL && s_cur < (((u128)1) << 82)) || esc_mid_bits[ci] < nxt2_fl_bl || esc_mid_bits[ci] <= 86))
                                    ? ((((u128)1) << esc_mid_bits[ci]) - 1)
                                    : n_hi;
                                u128 s_hi = (cut_hi < n_hi) ? cut_hi : n_hi;
                                if (s_hi < s_cur) continue;
                                int b_shi = bit_length_128(s_hi + 1);
                                int ks_sub = min_kd_for_jump(b_shi, nxt2_fl_bl);
                                if (ectx->kd_lo_monotone && ctx->kd_lo != 0 && ctx->kd_lo[b_shi] > ks_sub) ks_sub = ctx->kd_lo[b_shi];
                                if (ks_sub < b_shi) {
                                    int se_sub = k_n + ks_sub;
                                    if (se_sub >= k_coll) {
                                        if (se_sub < min_s_coll) min_s_coll = se_sub;
                                    } else {
                                        if ((!ectx->has_tight_win || nxt_req_lam == 0ULL || s_cur >= (((u128)1) << 82)) && s_cur >= (((u128)1) << (depth >= 2 ? 80 : 82))) {
                                            s_hi = n_hi;
                                            b_shi = bit_length_128(s_hi + 1);
                                            ks_sub = min_kd_for_jump(b_shi, nxt2_fl_bl);
                                            if (ectx->kd_lo_monotone && ctx->kd_lo != 0 && ctx->kd_lo[b_shi] > ks_sub) ks_sub = ctx->kd_lo[b_shi];
                                        }
                                        if (ks_sub < b_shi && (nxt_rem == ~0ULL || (step_term_lb_u128(s_hi, ks_sub) + ectx->tail_lb_q126[depth + 1]) < nxt_rem)) {
                                            if (!have_gn_nl) {
                                                if (!have_p3g) {
                                                    p3k_g_full = u256f_mul_u128(g_val, p3_kd);
                                                    have_p3g = 1;
                                                }
                                                g_n = u256f_add_u128(p3k_g_full, (((u128)1) << k_n) - sh_kkd_128);
                                                have_gn_nl = 1;
                                            }
                                            ectx->step_kd[depth] = kd;
                                            ectx->step_k_exp[depth] = k_exp;
                                            ectx->step_w_exp[depth] = w_exp;
                                            ectx->step_g_val[depth] = g_val;
                                            dfs_collect_gpu_esc_u128(fctx, depth + 1, k_n, w_n, g_n, s_cur, s_hi, nxt_rem, nxt_req_lam, l1_128, u1_128, span128, k_coll);
                                            if (ctx->aborted) return;
                                        }
                                    }
                                }
                                if (ci == 13 || s_hi >= n_hi) break;
                                s_cur = s_hi + 2;
                            }
                            if (min_s_coll < 1000) {
                                test_cong_esc_u128(ectx, base_diff_128 - (inv_wn << k_n), min_s_coll, l1_128, u1_128, span128);
                                if (ctx->aborted) return;
                            }
                        }
                    }
                }
            }
        }
    }
}

HENSEL_EXPORT int collect_hensel_gpu_frontier_c(
    const u384_io *n0_io,
    const u384_io *w_lo_io,
    const u384_io *w_hi_io,
    const u384_io *b2_io,
    int exact_r,
    int max_survivors_cap,
    u64 ulam_q126,
    u64 lam_lo_q126,
    int num_bands,
    const BandIO *bands,
    const int *kd_lo,
    const int *kd_hi,
    u64 max_budget,
    int split_depth,
    int max_gpu_tasks,
    GpuEscBoxParams *out_box_params,
    int *out_num_tasks,
    GpuHenselTask *out_tasks,
    u64 *out_nodes,
    u64 *out_leaf_ops,
    int *out_num_survivors,
    u384_io *out_survivors
) {
    ensure_stack_committed_win64();
    ensure_q126_tables();
    u384 n0_v = load_u384(n0_io);
    u384 b2_v = load_u384(b2_io);
    if (bit_length_fast(b2_v) > 126 || exact_r < 1 || exact_r > 9) return -6;
    GpuFrontierCtx fctx;
    memset(&fctx, 0, sizeof(fctx));
    fctx.split_depth = split_depth;
    fctx.max_tasks = max_gpu_tasks;
    fctx.out_tasks = out_tasks;
    EscStdCtx *ectx = &fctx.ectx;
    HenselCtx *ctx = &ectx->base;
    ectx->exact_r = exact_r;
    ectx->kd_lo_monotone = 1;
    ectx->has_tight_win = 0;
    ectx->lam_lo_q126 = lam_lo_q126;
    ectx->ulam_hi_q126 = ulam_q126;
    u384 b_hi_glob = (((u64)b2_v & 1ULL) != 0ULL) ? b2_v : (b2_v - 1);
    u128 b_hi_128 = (u128)b_hi_glob;
    for (int d = 0; d < exact_r; d++) {
        u384 wl_v = load_u384(&w_lo_io[d]);
        if (bit_length_fast(wl_v) > 126) return -6;
        ectx->floor_lo[d] = ((u128)wl_v) | (u128)1;
        if (d > 0 && ectx->floor_lo[d] < ectx->floor_lo[0]) ectx->kd_lo_monotone = 0;
        if (w_hi_io != 0) {
            u384 wh_v = load_u384(&w_hi_io[d]);
            if (bit_length_fast(wh_v) > 126) wh_v = b_hi_glob;
            u128 wh128 = (u128)wh_v;
            if (wh128 > b_hi_128) wh128 = b_hi_128;
            if (((u64)wh128 & 1ULL) == 0ULL && wh128 > 0) wh128 -= 1;
            ectx->ceil_hi[d] = wh128;
        } else {
            ectx->ceil_hi[d] = b_hi_128;
        }
        if (ectx->floor_lo[d] > ectx->ceil_hi[d]) {
            *out_num_tasks = 0;
            *out_nodes = 0;
            *out_leaf_ops = 0;
            *out_num_survivors = 0;
            return 0;
        }
        ectx->ceil_hi_bl[d] = bit_length_128(ectx->ceil_hi[d]);
        if (lam_lo_q126 > 0ULL && ectx->floor_lo[d] < (((u128)1) << 79)) {
            ectx->has_tight_win = 1;
        }
    }
    ectx->tail_ub_q126[exact_r] = 0ULL;
    ectx->tail_lb_q126[exact_r] = 0ULL;
    for (int s = exact_r - 1; s >= 0; s--) {
        u64 step_ub = inv_z_ub_exact_q126((u384)ectx->floor_lo[s]);
        int c_bl = bit_length_128(ectx->ceil_hi[s] + 1);
        int kd_min_s = (s + 1 < exact_r)
            ? min_kd_for_jump(c_bl, bit_length_128(ectx->floor_lo[s + 1]))
            : kd_hi[c_bl];
        if (ectx->kd_lo_monotone && kd_lo != 0 && kd_lo[c_bl] > kd_min_s) kd_min_s = kd_lo[c_bl];
        if (kd_min_s < 1) kd_min_s = 1;
        u64 step_lb = (kd_min_s < c_bl) ? step_term_lb_exact_q126((u384)ectx->ceil_hi[s], kd_min_s) : 0ULL;
        ectx->step_lb_q126[s] = step_lb;
        ectx->tail_ub_q126[s] = ectx->tail_ub_q126[s + 1] + step_ub;
        ectx->tail_lb_q126[s] = ectx->tail_lb_q126[s + 1] + step_lb;
        if (s == exact_r - 1) {
            ectx->min_ceil_idx[s] = s;
        } else {
            int prev_m = ectx->min_ceil_idx[s + 1];
            ectx->min_ceil_idx[s] = (ectx->ceil_hi[s] <= ectx->ceil_hi[prev_m]) ? s : prev_m;
        }
    }
    ctx->n0_threshold = n0_v;
    ctx->b_lo = (u384)ectx->floor_lo[0];
    ctx->b_hi = b_hi_glob;
    ctx->two_b_lo = 2 * ctx->b_lo;
    ctx->two_b_hi = 2 * b2_v;
    ctx->b_lo_bl = bit_length_fast(ctx->b_lo);
    ctx->b_hi_bl = bit_length_fast(b2_v);
    ctx->cur_r = exact_r;
    ctx->max_r_verify = exact_r;
    ctx->kd_lo = kd_lo;
    ctx->kd_hi = kd_hi;
    ctx->max_budget = max_budget;
    ctx->max_survivors = (max_survivors_cap > 0) ? max_survivors_cap : MAX_SURVIVORS;
    ctx->out_survivors = out_survivors;

    if (out_box_params != 0) {
        memset(out_box_params, 0, sizeof(*out_box_params));
        out_box_params->b_hi_0 = (u64)b_hi_128;
        out_box_params->b_hi_1 = (u64)(b_hi_128 >> 64);
        u128 two_b_hi_128 = (u128)ctx->two_b_hi;
        out_box_params->two_b_hi_0 = (u64)two_b_hi_128;
        out_box_params->two_b_hi_1 = (u64)(two_b_hi_128 >> 64);
        for (int d = 0; d < exact_r; d++) {
            out_box_params->floor_lo[d][0] = (u64)ectx->floor_lo[d];
            out_box_params->floor_lo[d][1] = (u64)(ectx->floor_lo[d] >> 64);
            out_box_params->ceil_hi[d][0] = (u64)ectx->ceil_hi[d];
            out_box_params->ceil_hi[d][1] = (u64)(ectx->ceil_hi[d] >> 64);
            out_box_params->ceil_hi_bl[d] = ectx->ceil_hi_bl[d];
        }
        for (int s = 0; s <= exact_r; s++) {
            out_box_params->step_lb_q126[s] = ectx->step_lb_q126[s];
            out_box_params->tail_ub_q126[s] = ectx->tail_ub_q126[s];
            out_box_params->tail_lb_q126[s] = ectx->tail_lb_q126[s];
            out_box_params->min_ceil_idx[s] = ectx->min_ceil_idx[s];
        }
        int kd_lim = ctx->b_hi_bl + 16;
        if (kd_lim > 158) kd_lim = 158;
        for (int k = 0; k <= kd_lim; k++) {
            out_box_params->kd_lo[k] = (kd_lo != 0) ? kd_lo[k] : 1;
            out_box_params->kd_hi[k] = kd_hi[k];
        }
        out_box_params->exact_r = exact_r;
        out_box_params->kd_lo_monotone = ectx->kd_lo_monotone;
        out_box_params->has_tight_win = ectx->has_tight_win;
        out_box_params->b_hi_bl = ctx->b_hi_bl;
    }

    u128 b_lo_0 = ectx->floor_lo[0];
    u128 b_hi_0 = ectx->ceil_hi[0];
    int b_hi_0_bl = ectx->ceil_hi_bl[0];

    for (int b = 0; b < num_bands; b++) {
        if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
            ctx->aborted = 1;
            break;
        }
        int k1 = bands[b].k1;
        if (k1 < 1 || k1 >= 120) return -5;
        ectx->root_k1 = k1;
        u384 lo1 = load_u384(&bands[b].lo1);
        u384 hi1 = load_u384(&bands[b].hi1);
        u384 u_min = load_u384(&bands[b].u_min);
        u384 u_max = load_u384(&bands[b].u_max);
        if (lo1 > hi1 || u_min > u_max) continue;
        u384 l1_p1 = lo1 + 1;
        u384 u1_p1 = hi1 + 1;
        u384 l_eff = shl384(u_min, k1);
        if (l_eff > l1_p1) l1_p1 = l_eff;
        u384 u_eff = shl384(u_max, k1);
        if (u_eff < u1_p1) u1_p1 = u_eff;
        if (l1_p1 > u1_p1) continue;
        if (bit_length_fast(u1_p1) > 86) return -5;

        u128 l1_128 = (u128)l1_p1;
        u128 u1_128 = (u128)u1_p1;
        if (((u64)l1_128 & 1ULL) != 0ULL) l1_128 += 1;
        if (((u64)u1_128 & 1ULL) != 0ULL) u1_128 -= 1;
        if (l1_128 > u1_128) continue;
        u128 span128 = u1_128 - l1_128;
        int k_coll = bit_length_128(span128);
        if (k_coll < 1) k_coll = 1;
        if (k_coll > 80) return -5;
        ctx->l_eff = (u384)l1_128;
        ctx->u_eff = (u384)u1_128;
        ctx->u_eff_bl = bit_length_128(u1_128);

        u128 u_min_eff = (l1_128 + g_mask128[k1]) >> k1;
        if (((u64)u_min_eff & 1ULL) == 0ULL) u_min_eff += 1;
        u128 u_max_eff = u1_128 >> k1;
        if (u_max_eff < u_min_eff) continue;
        if (((u64)u_max_eff & 1ULL) == 0ULL) u_max_eff -= 1;
        if (u_min_eff > u_max_eff) continue;

        u64 rem_ulam_1 = ~0ULL;
        u64 req_lam_1 = 0ULL;
        u128 root_blo = b_lo_0;
        u128 root_bhi = b_hi_0;
        if (ulam_q126 > 0ULL) {
            if (ectx->tail_lb_q126[0] >= ulam_q126) continue;
            u64 max_root_tau = ulam_q126 - ectx->tail_lb_q126[0];
            if (l1_128 < u1_128 && step_term_lb_exact_q126((u384)(l1_128 - 1), k1) >= max_root_tau) {
                if (step_term_lb_exact_q126((u384)(u1_128 - 1), k1) >= max_root_tau) continue;
                u128 l_cert = l1_128;
                u128 bs_lo = l1_128 + 2;
                u128 bs_hi = u1_128 - 2;
                for (int it = 0; it < 20 && bs_lo <= bs_hi; it++) {
                    u128 mid = (bs_lo + ((bs_hi - bs_lo) >> 1)) & ~(u128)1;
                    if (mid < bs_lo) mid = bs_lo;
                    if (step_term_lb_exact_q126((u384)(mid - 1), k1) >= max_root_tau) {
                        l_cert = mid;
                        bs_lo = mid + 2;
                    } else {
                        if (mid < 4) break;
                        bs_hi = mid - 2;
                    }
                }
                l1_128 = l_cert + 2;
                if (l1_128 > u1_128) continue;
                span128 = u1_128 - l1_128;
                k_coll = bit_length_128(span128);
                if (k_coll < 1) k_coll = 1;
                ctx->l_eff = (u384)l1_128;
                u_min_eff = (l1_128 + g_mask128[k1]) >> k1;
                if (((u64)u_min_eff & 1ULL) == 0ULL) u_min_eff += 1;
                if (u_min_eff > u_max_eff) continue;
            }
            u64 root_lb = step_term_lb_exact_q126((u384)(u1_128 - 1), k1);
            if ((root_lb + ectx->tail_lb_q126[0]) >= ulam_q126) continue;
            rem_ulam_1 = ulam_q126 - root_lb;
            u128 p1 = pole_min_next_u128(rem_ulam_1 - ectx->tail_lb_q126[1]);
            if (p1 > b_hi_0) continue;
            if (p1 > root_blo) root_blo = p1;
            int skip_b = 0;
            for (int t = 1; t < exact_r; t++) {
                u64 avail_t = rem_ulam_1 - (ectx->tail_lb_q126[0] - ectx->step_lb_q126[t]);
                if (pole_min_next_u128(avail_t) > ectx->ceil_hi[t]) {
                    skip_b = 1;
                    break;
                }
            }
            if (skip_b) continue;
        }
        if (lam_lo_q126 > 0ULL) {
            u64 root_max_ub = step_term_ub_exact_q126((u384)(l1_128 - 1), k1);
            if ((root_max_ub + ectx->tail_ub_q126[0]) < lam_lo_q126) continue;
            if (l1_128 < u1_128 && (step_term_ub_exact_q126((u384)(u1_128 - 1), k1) + ectx->tail_ub_q126[0]) < lam_lo_q126) {
                u128 u_cert = u1_128;
                u128 bs_lo = l1_128 + 2;
                u128 bs_hi = u1_128 - 2;
                for (int it = 0; it < 20 && bs_lo <= bs_hi; it++) {
                    u128 mid = (bs_lo + ((bs_hi - bs_lo) >> 1)) & ~(u128)1;
                    if (mid < bs_lo) mid = bs_lo;
                    if ((step_term_ub_exact_q126((u384)(mid - 1), k1) + ectx->tail_ub_q126[0]) < lam_lo_q126) {
                        u_cert = mid;
                        if (mid < 4) break;
                        bs_hi = mid - 2;
                    } else {
                        bs_lo = mid + 2;
                    }
                }
                if (u_cert < 2) continue;
                u1_128 = u_cert - 2;
                if (l1_128 > u1_128) continue;
                span128 = u1_128 - l1_128;
                k_coll = bit_length_128(span128);
                if (k_coll < 1) k_coll = 1;
                ctx->u_eff = (u384)u1_128;
                ctx->u_eff_bl = bit_length_128(u1_128);
                u_max_eff = u1_128 >> k1;
                if (u_max_eff < u_min_eff) continue;
                if (((u64)u_max_eff & 1ULL) == 0ULL) u_max_eff -= 1;
                if (u_min_eff > u_max_eff) continue;
            }
            root_max_ub = step_term_ub_exact_q126((u384)(l1_128 - 1), k1);
            if ((root_max_ub + ectx->tail_ub_q126[0]) < lam_lo_q126) continue;
            req_lam_1 = (lam_lo_q126 > root_max_ub) ? (lam_lo_q126 - root_max_ub) : 0ULL;
            if (req_lam_1 > ectx->tail_ub_q126[1]) {
                u128 p_mx1 = pole_max_cur_u128(req_lam_1 - ectx->tail_ub_q126[1]);
                if (p_mx1 < root_blo) continue;
                if (p_mx1 < root_bhi) {
                    root_bhi = (((u64)p_mx1 & 1ULL) != 0ULL) ? p_mx1 : (p_mx1 - 1);
                }
            }
        }
        if (root_blo > root_bhi) continue;
        u128 n_odd_u1 = ((u_max_eff - u_min_eff) >> 1) + 1;
        if (n_odd_u1 <= (u128)4096) {
            u64 sub_c = 0ULL;
            for (u128 uc = u_min_eff; uc <= u_max_eff; uc += 2) {
                if ((sub_c & 15ULL) == 0ULL) {
                    ctx->leaf_ops++;
                    if ((ctx->nodes + ctx->leaf_ops) > ctx->max_budget) {
                        ctx->aborted = 1;
                        break;
                    }
                }
                sub_c++;
                verify_z1_esc_u128(ectx, (uc << k1) - 1);
                if (ctx->aborted) break;
            }
            if (ctx->aborted) break;
            continue;
        }
        if (k1 > 80) return -5;
        u128 p3_k1 = g_p3_128[k1];
        u256f ev_max = u256f_sub1(mul128_to_256f(p3_k1, u_max_eff));
        u128 two_root_blo = root_blo << 1;
        if (u256f_lt_u128(ev_max, two_root_blo)) continue;
        u256f ev_min = u256f_sub1(mul128_to_256f(p3_k1, u_min_eff));
        if (u256f_lt_u128(ev_min, two_root_blo)) {
            ev_min.lo = two_root_blo;
            ev_min.hi = 0;
        }

        int root_bhi_bl = (root_bhi == b_hi_0) ? b_hi_0_bl : bit_length_128(root_bhi);
        int ld_s = bit_length_256f(ev_min) - root_bhi_bl;
        if (ld_s < 1) ld_s = 1;
        if (u256f_gt_u128(u256f_shr(ev_min, ld_s), root_bhi)) ld_s += 1;
        int ld_e = bit_length_256f(ev_max) - bit_length_128(root_blo) + 1;
        if (ld_e < ld_s) continue;

        u256f z2_mx = u256f_shr(ev_max, ld_s);
        u256f z2_mn = u256f_shr(ev_min, ld_s);
        for (int l1 = ld_s; l1 <= ld_e; l1++, z2_mx = u256f_shr1(z2_mx), z2_mn = u256f_shr1(z2_mn)) {
            if (u256f_lt_u128(z2_mx, root_blo)) break;
            if (u256f_gt_u128(z2_mn, root_bhi)) continue;
            if (k1 + l1 >= k_coll) {
                u128 r128 = (((u128)1) << k1) * (u128)g_inv3[k1];
                test_cong_esc_u128(ectx, r128 - l1_128, k1 + l1, l1_128, u1_128, span128);
                if (ctx->aborted) break;
                break;
            }
            u128 n_lo = u256f_le_u128(z2_mn, root_blo) ? root_blo : (z2_mn.lo | (u128)1);
            u128 n_hi = u256f_le_u128(z2_mx, root_bhi)
                ? ((((u64)z2_mx.lo & 1ULL) != 0ULL) ? z2_mx.lo : (z2_mx.lo - 1))
                : root_bhi;
            if (n_lo <= n_hi) {
                u256f g1 = {(((u128)1) << (k1 + l1)) - (((u128)1) << k1), (u128)0};
                int nxt1_fl_bl = (exact_r >= 2) ? bit_length_128(ectx->floor_lo[1]) : ctx->b_hi_bl;
                u128 s_cur = n_lo;
                for (int ci = 0; ci <= 13 && s_cur <= n_hi; ci++) {
                    u128 cut_hi = (ci < 13 && ((ectx->has_tight_win && req_lam_1 > 0ULL && s_cur < (((u128)1) << 82)) || esc_mid_bits[ci] < nxt1_fl_bl || esc_mid_bits[ci] <= 86))
                        ? ((((u128)1) << esc_mid_bits[ci]) - 1)
                        : n_hi;
                    u128 s_hi = (cut_hi < n_hi) ? cut_hi : n_hi;
                    if (s_hi < s_cur) continue;
                    dfs_collect_gpu_esc_u128(&fctx, 1, k1 + l1, k1, g1, s_cur, s_hi, rem_ulam_1, req_lam_1, l1_128, u1_128, span128, k_coll);
                    if (ctx->aborted) break;
                    if (ci == 13 || s_hi >= n_hi) break;
                    s_cur = s_hi + 2;
                }
                if (ctx->aborted) break;
            }
        }
        if (ctx->aborted) break;
    }
    if (ctx->aborted == 0 && (ctx->nodes + ctx->leaf_ops) > ctx->max_budget) ctx->aborted = 1;
    *out_num_tasks = fctx.num_tasks;
    *out_nodes = ctx->nodes;
    *out_leaf_ops = ctx->leaf_ops;
    *out_num_survivors = ctx->num_survivors;
    if (fctx.tasks_overflowed) return 2;
    return ctx->aborted;
}

HENSEL_EXPORT int verify_gpu_candidates_esc_c(
    const u384_io *n0_io,
    const u384_io *w_lo_io,
    const u384_io *w_hi_io,
    const u384_io *b2_io,
    int exact_r,
    int max_survivors_cap,
    int num_cands,
    const u64 *cands_u128_pairs,
    int *out_num_survivors,
    u384_io *out_survivors
) {
    ensure_q126_tables();
    u384 n0_v = load_u384(n0_io);
    u384 b2_v = load_u384(b2_io);
    if (bit_length_fast(b2_v) > 126 || exact_r < 1 || exact_r > 9) return -6;
    EscStdCtx ectx;
    memset(&ectx, 0, sizeof(ectx));
    HenselCtx *ctx = &ectx.base;
    ectx.exact_r = exact_r;
    u384 b_hi_glob = (((u64)b2_v & 1ULL) != 0ULL) ? b2_v : (b2_v - 1);
    u128 b_hi_128 = (u128)b_hi_glob;
    for (int d = 0; d < exact_r; d++) {
        u384 wl_v = load_u384(&w_lo_io[d]);
        ectx.floor_lo[d] = ((u128)wl_v) | (u128)1;
        if (w_hi_io != 0) {
            u384 wh_v = load_u384(&w_hi_io[d]);
            if (bit_length_fast(wh_v) > 126) wh_v = b_hi_glob;
            u128 wh128 = (u128)wh_v;
            if (wh128 > b_hi_128) wh128 = b_hi_128;
            if (((u64)wh128 & 1ULL) == 0ULL && wh128 > 0) wh128 -= 1;
            ectx.ceil_hi[d] = wh128;
        } else {
            ectx.ceil_hi[d] = b_hi_128;
        }
    }
    ctx->n0_threshold = n0_v;
    ctx->b_hi = b_hi_glob;
    ctx->max_survivors = (max_survivors_cap > 0) ? max_survivors_cap : MAX_SURVIVORS;
    ctx->num_survivors = *out_num_survivors;
    ctx->out_survivors = out_survivors;
    for (int i = 0; i < num_cands; i++) {
        u128 z = ((u128)cands_u128_pairs[2 * i]) | (((u128)cands_u128_pairs[2 * i + 1]) << 64);
        verify_z1_esc_u128(&ectx, z);
        if (ctx->aborted) break;
    }
    *out_num_survivors = ctx->num_survivors;
    return ctx->aborted;
}

#if defined(_WIN32)
int __stdcall _DllMainCRTStartup(void *h, unsigned r, void *p) {
    (void)h; (void)r; (void)p;
    return 1;
}
#endif
