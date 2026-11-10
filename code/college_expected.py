# -*- coding: utf-8 -*-
"""Data-based benchmark for partisan control: expected shares of condes and of county money by party if the 2024
mayors vote along party lines (plurality; ties split equally), with one vote per mayor and with population weights.
Writes out/college_expected.json."""
import os, json
import pandas as pd

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
m = pd.read_csv(os.path.join(ROOT, "data", "derived", "sc_master2.csv"))
J = m.health_region_2024.nunique()
popT = m.pop2022.sum()
cond, money, condp = {}, {}, {}
for r, df in m.groupby("health_region_2024"):
    cnt = df.party.value_counts()
    top = cnt[cnt == cnt.max()].index
    for p in top:
        cond[p] = cond.get(p, 0) + 1 / len(top) / J
        money[p] = money.get(p, 0) + df.pop2022.sum() / popT / len(top)
    w = df.groupby("party").pop2022.sum()
    topw = w[w == w.max()].index
    for p in topw:
        condp[p] = condp.get(p, 0) + 1 / len(topw) / J
srt = lambda d: dict(sorted(d.items(), key=lambda kv: -kv[1]))
out = {"expected_condes_1m1v": srt(cond), "money_1m1v": srt(money), "expected_condes_pop": srt(condp)}
json.dump(out, open(os.path.join(ROOT, "out", "college_expected.json"), "w"), indent=1, ensure_ascii=False)
print(json.dumps(out, indent=1, ensure_ascii=False))
