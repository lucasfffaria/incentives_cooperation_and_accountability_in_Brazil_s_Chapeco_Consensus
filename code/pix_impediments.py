# -*- coding: utf-8 -*-
"""Capacity gradient of completion from the 2025 special transfers to Santa Catarina municipalities.
Share of planned value with technical impediments by size class, and the elasticity of the share without
impediments to the capacity index (least squares of logs across the six classes, weighted by the number of plans). Writes out/pix_impediments.json."""
import os, json
import numpy as np, pandas as pd

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
m = pd.read_csv(os.path.join(ROOT, "data", "derived", "sc_master2.csv"))
p = pd.read_csv(os.path.join(ROOT, "data", "companion", "sc_pix2025_plans.csv"))
p = p[p.codigo_ibge_municipio.notna()].copy()
p["ibge_id"] = p.codigo_ibge_municipio.astype(int)
p = p.merge(m[["ibge_id", "size_class", "kappa"]], on="ibge_id", how="inner")
p["imp"] = p.situacao_plano_acao.str.startswith("IMPEDIDO")
order = ["<5k", "5-10k", "10-20k", "20-50k", "50-100k", ">100k"]
rows = []
for c in order:
    q = p[p.size_class == c]
    imp = float((q.valor_plano * q.imp).sum() / q.valor_plano.sum())
    kap = float(m.loc[m.size_class == c, "kappa"].mean())
    rows.append(dict(cls=c, n_plans=int(len(q)), imp_value=imp, share_without_impediments=1 - imp, kappa=kap))
x = np.log([r["kappa"] for r in rows])
y = np.log([r["share_without_impediments"] for r in rows])
n = np.array([r["n_plans"] for r in rows], float)


def wls(x, y, w):
    """Slope of a least-squares fit weighted by the number of plans in each class."""
    X = np.column_stack([np.ones_like(x), x])
    return float(np.linalg.solve(X.T @ (w[:, None] * X), X.T @ (w * y))[1])


nu_all = wls(x, y, n)
nu_excl = wls(x[:-1], y[:-1], n[:-1])
out = dict(by_class=rows, nu_all=nu_all, nu_excl_large=nu_excl)
json.dump(out, open(os.path.join(ROOT, "out", "pix_impediments.json"), "w"), indent=1)
print(json.dumps(out, indent=1))
