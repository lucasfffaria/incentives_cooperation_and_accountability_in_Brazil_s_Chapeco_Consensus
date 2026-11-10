# -*- coding: utf-8 -*-
"""Between-state consequences of moving individual amendments to counties with a national
per-capita rule (real data: Chamber apportionment, LC 78/1993; Census 2022; 2025 quotas)."""
import json, pandas as pd, numpy as np
seats = dict(SP=70,MG=53,RJ=46,BA=39,RS=31,PR=30,PE=25,CE=22,MA=18,GO=17,PA=17,SC=16,PB=12,ES=10,PI=10,AL=9,
             AC=8,AP=8,AM=8,DF=8,MS=8,MT=8,RN=8,RO=8,RR=8,SE=8,TO=8)
pop = dict(RO=1581196,AC=830018,AM=3941613,RR=636707,PA=8120131,AP=733759,TO=1511460,MA=6776699,PI=3271199,
           CE=8794957,RN=3302729,PB=3974687,PE=9058931,AL=3127683,SE=2210004,BA=14141626,MG=20539989,ES=3833712,
           RJ=16055174,SP=44411238,PR=11444380,SC=7610361,RS=10882965,MS=2757013,MT=3658649,GO=7056495,DF=2817381)
QD, QS = 37.2e6, 68.5e6
d = pd.DataFrame({"seats":seats,"pop":pop}); d["senators"]=3
assert d.seats.sum()==513 and d["pop"].sum()==203080756
d["dep_amend"] = QD*d.seats; d["all_amend"] = d.dep_amend + QS*d.senators
for col,lab in (("dep_amend","dep"),("all_amend","all")):
    tot = d[col].sum(); d[f"pc_sq_{lab}"] = d[col]/d["pop"]
    d[f"pc_reform_{lab}"] = tot/d["pop"].sum()
    d[f"change_{lab}"] = d[f"pc_reform_{lab}"]/d[f"pc_sq_{lab}"]-1
d["seat_share"]=d.seats/513; d["pop_share"]=d["pop"]/d["pop"].sum()
d = d.sort_values("change_dep")
print(d[["seats","pop","pc_sq_dep","pc_reform_dep","change_dep","pc_sq_all","change_all"]].round(3).to_string())
lose_dep = d.change_dep<0; lose_all = d.change_all<0
summary = dict(
  states_losing_dep=int(lose_dep.sum()), seats_in_losing_states_dep=int(d.seats[lose_dep].sum()), senators_in_losing_states_dep=int(3*lose_dep.sum()),
  states_losing_all=int(lose_all.sum()), seats_in_losing_states_all=int(d.seats[lose_all].sum()), senators_in_losing_states_all=int(3*lose_all.sum()),
  national_pc_dep=float(d.pc_reform_dep.iloc[0]), national_pc_all=float(d.pc_reform_all.iloc[0]),
  sc_change_dep=float(d.loc["SC","change_dep"]), sc_change_all=float(d.loc["SC","change_all"]),
  max_gain_dep=(d.change_dep.idxmax(), float(d.change_dep.max())), max_loss_dep=(d.change_dep.idxmin(), float(d.change_dep.min())),
  max_gain_all=(d.change_all.idxmax(), float(d.change_all.max())), max_loss_all=(d.change_all.idxmin(), float(d.change_all.min())),
  ratio_max_min_pc_sq_all=float(d.pc_sq_all.max()/d.pc_sq_all.min()))
print(json.dumps(summary, indent=1))
d.to_csv("../out/national_accounting.csv"); json.dump(summary, open("../out/national_accounting.json","w"), indent=1)
