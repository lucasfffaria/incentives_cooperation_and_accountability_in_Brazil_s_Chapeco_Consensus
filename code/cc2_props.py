# -*- coding: utf-8 -*-
"""Brute-force verification of Propositions 1-7 of CC-2 against their closed forms. Writes out/cc2_props.json."""
import os, json
import numpy as np
from scipy.special import expit
from scipy.stats import norm
from scipy.optimize import brentq
from cc2_chamber import r_corr, r_corr_B, top_mean

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
rng = np.random.default_rng(11)
res = {}

# ---------------------------------------------------------------- P1: selection on a noisy index
errs, errsB = [], []
for _ in range(40):
    t, s, rho = rng.uniform(0.1, 3), rng.uniform(0.2, 3), rng.uniform(-0.4, 0.7)
    S = int(rng.choice([1, 2, 3, 6]));
    N = S * int(rng.integers(2, 6))
    n = 60000
    L = rng.standard_normal((n, N));
    B = rho * L + np.sqrt(1 - rho ** 2) * rng.standard_normal((n, N))
    I = L + t * B + s * rng.standard_normal((n, N))
    top = np.argsort(-I, axis=1)[:, :S]
    emp = np.take_along_axis(L, top, 1).mean();
    empB = np.take_along_axis(B, top, 1).mean()
    a = top_mean(S, N)
    errs.append(abs(emp - r_corr(t, s, rho) * a));
    errsB.append(abs(empB - r_corr_B(t, s, rho) * a))
res["P1_max_abs_err_legislative_skill"] = float(max(errs))
res["P1_max_abs_err_brokerage_skill"] = float(max(errsB))
# derivative sign: dr/dt < 0 iff t > rho s^2 / (1 - rho^2)
bad = 0
for _ in range(2000):
    t, s, rho = rng.uniform(0.01, 4), rng.uniform(0, 3), rng.uniform(-0.9, 0.9)
    h = 1e-6
    der = (r_corr(t + h, s, rho) - r_corr(t - h, s, rho)) / (2 * h)
    tstar = rho * s ** 2 / (1 - rho ** 2)
    if abs(t - tstar) > 1e-3 and (der < 0) != (t > tstar):
        bad += 1
res["P1_derivative_sign_violations"] = bad

# ---------------------------------------------------------------- P2: effort with relocation
viol = 0;
maxerr = 0
for _ in range(2000):
    s0, pi, ka, eta, chi, sp = rng.uniform(0.5, 0.8), rng.uniform(0.2, 2), rng.uniform(0.5, 2), rng.uniform(0, 1), \
                               rng.uniform(0, 1), rng.uniform(0, 1)
    WB, WL = s0, 1 - s0
    psi = eta + chi * (1 - eta) * sp
    e = np.linspace(1e-4, 1 - 1e-4, 200001)
    U = pi * psi * WB * np.log(e) + ka * WL * np.log(1 - e)
    e_num = e[np.argmax(U)]
    X = pi * psi / ka
    e_cf = X * s0 / (X * s0 + 1 - s0)
    maxerr = max(maxerr, abs(e_num - e_cf))
    if ((1 - e_cf) > (1 - s0)) != (X < 1) and abs(X - 1) > 1e-6:
        viol += 1
res["P2_max_abs_err_effort"] = float(maxerr)
res["P2_condition_violations"] = viol

# ---------------------------------------------------------------- P4: completion hurdle (technical conde)
viol = 0
for _ in range(20000):
    q, sig, f, dc, vbar, vinc, abar, bd = rng.uniform(0.2, 1), rng.uniform(-0.5, 0.8), rng.uniform(0.7, 1), \
                                          rng.uniform(0, 0.15), rng.uniform(0.6, 0.95), rng.uniform(0.1, 0.5), \
                                          rng.uniform(0, 0.6), rng.uniform(0.7, 0.9)
    C = 1.0;
    V = (1 + sig) * C;
    spent = f * C
    unf = (1 - abar) * (q * bd * V + (1 - q) * vinc * spent) + abar * vinc * spent
    EV = (1 - dc) * (q * V + (1 - q) * unf)
    invest = EV - vbar * spent > 0
    q_eff = q + (1 - q) * (1 - abar) * q * bd
    s_w = (1 - q) * ((1 - abar) * (1 - q) + abar) * vinc
    hurdle = f * (vbar / (1 - dc) - s_w) / q_eff - 1
    if abs(sig - hurdle) > 1e-9 and invest != (sig > hurdle):
        viol += 1
res["P4_hurdle_violations"] = viol
# hurdle falls with completion (numerical derivative over the prior box)
neg = 0;
tot = 0
for _ in range(5000):
    f, dc, vbar, vinc, abar, bd = rng.uniform(0.7, 1), rng.uniform(0, 0.15), rng.uniform(0.6, 0.95), \
                                  rng.uniform(0.1, 0.5), rng.uniform(0, 0.6), rng.uniform(0.7, 0.9)
    hs = []
    for q in (0.4, 0.4001):
        q_eff = q + (1 - q) * (1 - abar) * q * bd
        s_w = (1 - q) * ((1 - abar) * (1 - q) + abar) * vinc
        hs.append(f * (vbar / (1 - dc) - s_w) / q_eff - 1)
    tot += 1;
    neg += hs[1] < hs[0]
res["P4_hurdle_decreasing_in_completion_share"] = neg / tot

# ---------------------------------------------------------------- P3: cooperation best response and threshold
viol = 0
for _ in range(20000):
    gam, w, V, dq, epx, qc, delta, F, stake, s = rng.uniform(-0.3, 0.7), rng.uniform(0, 0.5), rng.uniform(1, 20), \
                                                 rng.uniform(0, 0.5), rng.uniform(0, 1), rng.uniform(0, 1), \
                                                 rng.uniform(0, 1), rng.uniform(0, 10), rng.uniform(0.01, 5), \
                                                 rng.uniform(0.1, 2)
    NG = (1 + gam) * w * V * (dq + epx * qc) + delta * F - stake
    # simulate logistic shocks
    p_emp = (NG + rng.logistic(0, s * stake, 4000) >= 0).mean()
    p_cf = expit(NG / (s * stake))
    if abs(p_emp - p_cf) > 0.04:
        viol += 1
    dstar = (stake - (1 + gam) * w * V * (dq + epx * qc)) / F if F > 0 else np.inf
    if F > 0 and abs(delta - dstar) > 1e-9 and ((p_cf >= 0.5) != (delta >= dstar)):
        viol += 1
res["P3_violations"] = viol
# engine check: the equilibrium returned by coop_equilibrium is a fixed point of the best response
from cc2_data import Geo
from cc2_params import sample, CONST
from cc2_model import coop_equilibrium

geo = Geo()
Wn, K, n = 50, 4, 12
P, _ = sample(Wn, seed=5)
Q = rng.uniform(0.5, 0.95, (Wn, K));
C = rng.uniform(1, 5, (Wn, K));
V = C * rng.uniform(0.9, 1.4, (Wn, K))
w = rng.dirichlet(np.ones(n), (Wn, K));
hostm = np.zeros((Wn, K, n), bool);
hostm[:, :, 0] = True
part = (w >= 0.02) | hostm
wt = np.where(part, w, 0);
wt = wt / wt.sum(-1, keepdims=True)
chi = 0.3
stake = np.where(part, (1 + P["ell"])[:, None, None] * chi * C[..., None] * wt, 0) + hostm * 0.05 * C[..., None]
gt = 1 + rng.uniform(-0.2, 0.3, (Wn, n));
dF = rng.uniform(0, 0.5, (Wn, n))
p, qx, A, Hk, Fk = coop_equilibrium(Q, V, C, w, wt, part, hostm, stake, gt, dF, P, chi, iters=60)
p2, *_ = coop_equilibrium(Q, V, C, w, wt, part, hostm, stake, gt, dF, P, chi, iters=61)
res["P3_engine_fixed_point_residual"] = float(np.abs(p - p2)[part].max())
# comparative statics in the engine: more future value or more excludability never lowers cooperation
pA, *_ = coop_equilibrium(Q, V, C, w, wt, part, hostm, stake, gt, dF * 2, P, chi, iters=60)
P2 = dict(P);
P2["eps_x"] = np.minimum(1, P["eps_x"] + 0.3)
pB, *_ = coop_equilibrium(Q, V, C, w, wt, part, hostm, stake, gt, dF, P2, chi, iters=60)
res["P3_engine_mean_change_more_future"] = float((pA - p)[part].mean())
res["P3_engine_mean_change_more_excludable"] = float((pB - p)[part].mean())

# ---------------------------------------------------------------- P5: effort, band and crowding out
viol = 0;
maxerr = 0
for _ in range(3000):
    th, au, Y, ce, em = rng.uniform(0.2, 1), rng.uniform(0, 0.3), rng.uniform(0, 1), rng.uniform(0.02, 0.3), \
                        rng.uniform(0, 1)
    eu = np.linspace(0, 1, 100001)
    U = th * au * eu * Y - ce * (em + eu) ** 2 / 2
    num = eu[np.argmax(U)]
    cf = np.clip(th * au * Y / ce - em, 0, 1)
    maxerr = max(maxerr, abs(num - cf))
res["P5_crowding_out_max_abs_err"] = float(maxerr)
# band: marginal pass incentive phi((mu - zbar)/sn)/sn is maximal at the threshold and symmetric
mus = np.linspace(-3, 3, 601)
mi = norm.pdf(mus / 0.5) / 0.5
res["P5_band_peak_at_threshold"] = float(mus[np.argmax(mi)])

# ---------------------------------------------------------------- P6: pre-election tilt (water-filling)
viol = 0;
gaps = []
for _ in range(300):
    m = int(rng.integers(3, 8))
    A = rng.uniform(0, 2, m);
    rev = rng.uniform(0.5, 3, m);
    h = rng.uniform(0.02, 0.1);
    lam = rng.uniform(0.05, 1)
    T_cf = np.maximum(A * h / lam - h * rev, 0)

    def obj(T):
        return (A * h * np.log1p(T / (h * rev))).sum() - lam * T.sum()

    best = obj(T_cf)
    for _ in range(300):
        Tp = np.maximum(T_cf + rng.normal(0, 0.05, m) * (1 + T_cf), 0)
        if obj(Tp) > best + 1e-9:
            viol += 1
            break
res["P6_waterfilling_violations"] = viol

# ---------------------------------------------------------------- P7: the sanction trap (fixed points)
def gamma_map(c, mu, bar, kap, Q=0.9, g0=-1.5, beta=0.6, pw=0.9, F=4.0, s=0.4, b=6.0, zbar=0.0, sn=0.5):
    Pi = norm.cdf((mu + b * c - zbar) / sn)
    cont = pw * (kap + (1 - kap) * Pi) if bar else pw
    return Q * expit((g0 + beta * cont * F) / s)


def fixed_points(mu, bar, kap):
    cs = np.linspace(0, 1, 2001)
    g = np.array([gamma_map(c, mu, bar, kap) for c in cs]) - cs
    roots = []
    for i in range(len(cs) - 1):
        if g[i] == 0 or g[i] * g[i + 1] < 0:
            roots.append(brentq(lambda c: gamma_map(c, mu, bar, kap) - c, cs[i], cs[i + 1]))
    return roots


multi_bar = [mu for mu in np.linspace(-5, 1.5, 131) if len(fixed_points(mu, True, 0.2)) >= 3]
multi_nobar = [mu for mu in np.linspace(-5, 1.5, 131) if len(fixed_points(mu, False, 0.2)) >= 3]
res["P7_capacity_range_with_multiple_steady_states_bar"] = [float(min(multi_bar)), float(max(multi_bar))] \
    if multi_bar else []
res["P7_multiple_steady_states_without_bar"] = len(multi_nobar)
# the bar lowers the map everywhere when kap < 1
cs = np.linspace(0, 1, 101)
res["P7_bar_lowers_map_everywhere"] = bool(all(gamma_map(c, mu, True, 0.5) <= gamma_map(c, mu, False, 0.5) + 1e-12
                                               for c in cs for mu in np.linspace(-2, 2, 21)))
res["P7_example_fixed_points"] = {f"{mu:.1f}": [round(x, 3) for x in fixed_points(mu, True, 0.2)]
                                  for mu in (-4.0, -3.0, -2.5, -2.0, -1.5, 0.0)}
json.dump(res, open(os.path.join(ROOT, "out", "cc2_props.json"), "w"), indent=1)
print(json.dumps(res, indent=1))
