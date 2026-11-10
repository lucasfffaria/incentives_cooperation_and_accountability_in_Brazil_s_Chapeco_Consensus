| Parameter | Group | Description | Prior (uniform) | Source or anchor |
|---|---|---|---|---|
| `s0` | Chamber | status-quo share of deputies' effort on brokerage | [0.5, 0.8] | premise P1; unmeasured |
| `pi` | Chamber | list-makers' weight on brokerage relative to voters' | [0.2, 1.2] | assumption |
| `kappa` | Chamber | list-makers' weight on legislation relative to voters' | [0.5, 2] | assumption |
| `t0` | Chamber | voters' weight on brokerage skill relative to legislative skill (open list) | [0.5, 2] | assumption |
| `rho_LB` | Chamber | correlation between legislative and brokerage skill | [−0.3, 0.5] | assumption |
| `sig_eps` | Chamber | noise in personal votes, relative to the weight on legislative skill | [1, 3] | assumption |
| `sig_nu` | Chamber | list-makers' idiosyncratic criteria (loyalty, faction) | [0.5, 3] | assumption; Jones et al. (2002) |
| `k_asp` | Chamber | serious aspirants per seat | [2, 5] | assumption |
| `gam_L` | Chamber | legislative productivity per SD of legislative skill | [0.1, 0.3] | assumption |
| `eta_X` | Relocation | share of abolished amendment money re-created in discretionary channels | [0, 1] | Rapporteur-amendment (RP9) episode 2022-23: half to individual amendments, half to ministries; committee amendments R$0.3 bn (2022) to R$6.9 bn (2023) and R$14.2 bn (2024) (Ronconi et al. 2025) |
| `chi_c` | Relocation | responsiveness of a co-partisan conde to deputies' requests | [0, 1] | assumption |
| `s_bar` | Projects | cost of candidate regional projects / county money of a term | [0.3, 1] | assumption |
| `sig_bar` | Projects | mean net scale economies of regional projects | [−0.1, 0.3] | Bel & Warner (2015); Bel & Sebő (2021) |
| `sd_sig` | Projects | dispersion of scale economies across projects | [0.1, 0.3] | assumption |
| `p_polo` | Projects | probability that a project is hosted by the county's largest city | [0.4, 0.8] | assumption |
| `D0` | Projects | distance decay of project benefits (km) | [30, 90] | assumption |
| `c_host` | Projects | host's local cost (land, permits, opposition), share of project cost | [0, 0.1] | assumption |
| `kap_cred` | Projects | conde's private credit per real of regional investment | [0, 0.3] | assumption; Litschig (2012) credit logic |
| `q_loc0` | Implementation | completion of transfer-funded municipal works within a term | [0.55, 0.8] | TCU (2019): 37.5% paralyzed or unfinished; TCU (2023): 41% (SC 38.9%) |
| `nu` | Implementation | elasticity of completion to technical capacity | [0, 0.3] | 2025 special transfers to SC: planned value with technical impediments 23% (<5,000 inh.) to 10-12% (20,000-100,000); implied elasticity 0.13-0.17 |
| `phi_cx` | Implementation | completion penalty of regional (complex) projects | [0, 0.3] | assumption |
| `g_pool` | Implementation | share of the capacity gap closed by a county technical team | [0, 0.5] | assumption |
| `alpha_e` | Implementation | proportional gain in completion at full supervision effort | [0.1, 0.5] | assumption |
| `c_e` | Implementation | conde's cost of full effort (share of term budget) | [0.02, 0.2] | assumption |
| `v_inc` | Implementation | salvage value of an abandoned work per real | [0.1, 0.5] | assumption |
| `a_ab` | Implementation | abandonment of unfinished projects when the conde's party changes | [0.2, 0.6] | assumption; disruption after turnover (Akhtari et al. 2022) |
| `a_same` | Implementation | abandonment when the conde changes within the same party | [0, 0.2] | assumption |
| `beta_d` | Implementation | value of a work completed one term late, per real of on-time value | [0.7, 0.9] | assumption |
| `c_adm` | Implementation | county administration, share of county money | [0.01, 0.04] | assumption |
| `alpha_u` | Implementation | value gain of completed projects from unmeasured quality effort | [0, 0.2] | assumption; multitask (Holmstrom & Milgrom 1991) |
| `alpha_a` | Implementation | completion gain per SD of the conde's competence | [0, 0.15] | assumption |
| `omega_h` | Cooperation | completion lost if the host obstructs | [0.2, 0.6] | assumption |
| `nu_c` | Cooperation | elasticity of completion to the share of the project's cost funded | [1, 3] | assumption; TCU: insufficient counterpart funds |
| `eps_x` | Cooperation | excludability of benefits / enforcement against non-payers | [0, 0.5] | assumption; Law 11.107/2005 (exclusion of defaulting members) |
| `zeta_opp` | Cooperation | discount on benefits credited to a rival party's conde | [0, 0.4] | assumption; alignment and adoption (Macinko et al. 2010) |
| `s_shock` | Cooperation | scale of private cost shocks relative to the mayor's stake | [0.25, 1] | assumption |
| `ell` | Cooperation | mayors' localism premium | [0, 0.5] | Gerber & Gibson (2009); Ten Cate (2023) |
| `gam` | Cooperation | credit for regional projects accruing to participating mayors | [0, 0.3] | assumption |
| `beta_y` | Cooperation | annual discount factor | [0.85, 0.95] | assumption |
| `theta_lo` | Conde | lower bound of condes' weight on value (theta ~ U[theta_lo, 1]) | [0.2, 0.7] | assumption |
| `V_R` | Conde | value of reappointment to the conde, share of term budget | [0, 0.3] | assumption |
| `rho_R` | Conde | retrospective weight of mayors' gains in the college vote (logit) | [0, 3] | assumption; Ferraz & Finan (2008) for voters |
| `phi_P` | Conde | party loyalty in the college vote (logit) | [1.5, 4] | Novaes (2018): 31-39% of mayors switch parties |
| `kap_party` | Conde | share of a conde's commitments honored by a co-partisan successor | [0.3, 1] | assumption |
| `c_T` | Conde | conde's cost per real moved in the pre-election tilt | [0, 0.5] | assumption |
| `alpha_V` | Conde | electoral return to local money (logit per unit of revenue) | [0.5, 6] | Litschig & Morrison (2013): +10 points of incumbent-party re-election (base 0.17) for 20% more spending; about 3.5 logit points per unit (conversion in Section S4.8; 95% interval about 0.1-5.9) |
| `h_V` | Conde | scale of diminishing electoral returns (share of revenue) | [0.02, 0.1] | assumption |
| `r_run` | Municipal | eligible incumbents who run | [0.69, 0.708] | SC 2020: 0.690; 2024: 0.708 |
| `p_win0` | Municipal | incumbents who run and win | [0.669, 0.742] | SC 2024: 0.669; 2020: 0.742 |
| `h_sw` | Municipal | switching hazard of running incumbents | [0.18, 0.45] | calibrated: re-elected mayors who changed party, SC 2020: 0.136; 2024: 0.349 |
| `beta_bw` | Municipal | bandwagon toward the conde's party (switchers and open seats) | [0, 0.3] | assumption; 62% of 2024 switchers joined the governor's party |
| `r_keep` | Municipal | open seats kept by the outgoing mayor's party | [0.148, 0.185] | SC 2020: 0.148; 2024: 0.185 (incumbent not running) |
| `c_dir` | Municipal | precision of the statewide partisan climate at each election (Dirichlet) | [10, 40] | calibrated: change in mayors' party shares, SC 2016-20: 0.15; 2020-24: 0.23 |
| `f_SC` | Diversion | Santa Catarina factor on municipal diversion rates | [0.5, 1] | Ferraz & Finan (2011): 0.055 eligible, 0.074 term-limited |
| `d_c0` | Diversion | baseline diversion and capture in county procurement | [0.04, 0.12] | Ferraz & Finan (2011); lower part of the 5-23% model-implied corruption tax on firms in Colonnelli & Prem (2022) |
| `D_max` | Diversion | discipline from a contestable reappointment | [0.15, 0.5] | Ferraz & Finan (2011): 27-36% |
| `g_ten` | Diversion | rise in capture per extra term of party tenure | [0, 0.3] | assumption |
| `w_cap` | Targets | share of capacity in the county score | [0.3, 0.6] | assumption |
| `w_noise` | Targets | share of noise in the county score | [0.2, 0.5] | Kane & Staiger (2002) |
| `phi_c` | Targets | share of counties failing at baseline | [0.1, 0.3] | design (open in the proposal) |
| `s_T` | Targets | share of next-term money withheld from a failing county | [0.2, 0.6] | design (proposal: loss of access to new resources) |
| `Xi` | Targets | Union's resolve to enforce territorial sanctions | [1.5, 3] | assumption |
| `varrho` | Targets | need gradient of the harm from withholding money | [0.5, 1.5] | assumption |
| `p_I` | LRG | efficacy of inspection (share of attempts blocked) | [0, 0.3] | Olken (2007); Avis et al. (2018) |
| `s_D` | LRG | penalty per real when diversion is detected | [0, 2] | assumption |
| `g_TA` | LRG | completion gain from technical assistance at zero capacity | [0, 0.3] | Lautharte et al. (2021); companion paper |
| `c_A` | LRG | cost of commissioners per real overseen | [0, 0.03] | companion paper: R$350k per year |
| `zeta` | Need | inequality aversion in need-weighted value | [0, 1] | assumption |
| `u_contract` | Design | share of non-excludable benefit made enforceable by contracts (R3) | [0.5, 0.9] | assumption; Kresch (2020) |
| `gam_cb` | Design | credit shared with participating mayors under co-branding (R4) | [0.3, 0.7] | assumption |
| `e_cap` | Design | share of relocation blocked by a cap on discretionary channels (R13) | [0.3, 0.9] | assumption |
