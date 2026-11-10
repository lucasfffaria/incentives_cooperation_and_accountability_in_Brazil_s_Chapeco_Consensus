# Replication package

**Incentives, cooperation and accountability in Brazil's "Chapecó Consensus"**

This package reproduces every number, table and figure of the article and of its Supplementary Material. It is the folder `Replication_Package` of the Supplementary Material and is laid out to be published as a repository (for example on GitHub) for external audit.

## Contents

| Folder or file | Contents |
|---|---|
| `run_all.sh` | Rebuilds every output, table and figure. About 20 minutes on the test machine used for the study. |
| `code/` | The model and the experiment (Python). `cc2_model.py` is the county game and the municipal module, `cc2_chamber.py` the Chamber module, `cc2_params.py` the 71 parameters with their priors, groups and sources (Table S4), `cc2_data.py` the geography, parties and status quo, `cc2_run.py` the main experiment (2,000 worlds × 21 designs), `cc2_mech.py` the instrumented run of 300 worlds (Figures 6a, 7a, 7c and the mechanism statistics), `cc2_props.py` the brute-force checks of the propositions (Table S2), `cc2_tests_engine.py` the engine tests, `cc2_analyze.py` and `cc2_textnums.py` the summary statistics and every conditional number quoted in the text, `cc2_robust.py` the robustness checks (Table S8), `cc2_gsa.py` the Morris screening and grouped Sobol' indices (Table S9, Figure S4), `cc2_tables.py` the tables (saved in `out/tables/`), and `fig_*.py` the figures (saved in `figs/`). `prep_tse.py` prepares the TSE votes for federal deputy, `prep_data2.py` the municipal data and the status quo (with `targeting.py`, the regression of deputies' transfers on their votes), `electoral_connection.py` the evidence of Supplementary Material 07 (Section S7.2), and `pix_impediments.py`, `college_expected.py`, `real_colleges.py` and `national_accounting.py` the other data-based results. |
| `data/` | Real data for Santa Catarina. `data/companion/` holds the election, fiscal and amendment files taken from the companion evaluation of the managerial law. `sc_master.csv` holds population, GDP, coordinates and the 2024 mayors, `sc_health_regions_2024.csv` the 17 health regions and 8 macro-regions of Deliberation 38/CIB/2024, and `geojs-42-mun.json` the municipal boundaries (IBGE mesh, used only to draw maps). Supplementary Material 04 (Section S4.1 and Table S3) gives the source of each dataset. `data/derived/` is produced by `prep_tse.py` (`tse_fed_2022.csv`, `tse_fed_2026.csv`, `tse_summary.json`: votes for federal deputy by candidate and municipality, and the 2026 seats) and `prep_data2.py` (the municipal master file, the status-quo allocations `sq_alloc.npz` with keys `main`, `pooled_low`, `pooled`, `health` and `chamber2026`, and `data_stats.json`). `data/raw_tse/` is where the TSE files `votacao_candidato_munzona_2022_SC.csv` and `votacao_candidato_munzona_2026_SC.csv` go to rebuild the vote files from scratch (they keep the names under which the TSE distributes them and are not redistributed here); without them `prep_tse.py` uses the derived files. |
| `out/` | All outputs. `cc2_worlds.npz` holds one value per world for every design and indicator (keys `DESIGN|indicator`) and the parameter draws (keys `P|name`); `cc2_mun.npz` and `cc2_mech.npz` hold the values by municipality and the instrumented run; `cc2_numbers.json` and `cc2_text_numbers.json` hold the numbers quoted in the text; `out/tables/` holds the generated tables in Markdown, one file per table, named after its number in the article or the Supplementary Material (`table2.md` is Table 2, `tableS4.md` is Table S4); the other `.json` files hold the propositions checks, robustness checks, sensitivity analyses, scenario discovery, calibration checks and data-based results. The `.log` files are the logs of the last complete run. |
| `lean/` | Machine-checked proofs, in Lean 4 with the Mathlib library, of the mathematical statements of Propositions 1–7 and Supplementary Propositions 8–9 (Supplementary Material 03). `lean/README.md` explains how to build them (`lake exe cache get`, then `lake build`), gives the Lean theorem that corresponds to each statement and step of the proofs, and states what is taken as a hypothesis or left out: in Proposition 1, the independence between the indices and the residual of skill after its projection on them, which joint normality implies but Mathlib cannot yet state; in Proposition 3, the existence of an equilibrium, obtained from Brouwer's theorem; in Proposition 7, the stability of the steady states. An audit module makes the build fail if any proof is incomplete or depends on a nonstandard axiom; `lean/results/lake_build_output.txt` is the output of the check. The build is independent of `run_all.sh`. |

Every file is included unpacked; none is larger than 24 MB (the largest is `out/cc2_worlds.npz`, 23 MB), so the package fits a standard Git repository without large-file storage. `.gitignore` excludes the figures that `run_all.sh` draws (`figs/`), the raw TSE files, the Python cache and the Lean build folder (`lean/.lake/`).

## How to run

Requirements: Python 3.11 or later with numpy, scipy, pandas, statsmodels, scikit-learn, matplotlib and geopandas (the results were produced with Python 3.13, numpy 2.5, scipy 1.18, pandas 3.0, statsmodels 0.15, scikit-learn 1.9, matplotlib 3.11 and geopandas 1.2).

```bash
sh run_all.sh        # rewrites out/ (with out/tables/) and figs/
```

The steps are, in order: data preparation, engine tests, propositions, main experiment (about seven minutes), instrumented run, analysis and text numbers, robustness checks, sensitivity analyses for the proposal (R0) and the robust variant (R15), figures and tables. Every random draw is seeded. A second, clean run of the pipeline in a fresh copy of the package reproduced every output file (the sensitivity files differ only in their recorded run time).

To check the proofs of the propositions, install `elan`, the Lean version manager, and run `lake exe cache get` and `lake build` in `lean/` (see `lean/README.md`). The first command downloads the compiled Mathlib library; the build then takes a few minutes and ends with the message of the audit module, as in `lean/results/lake_build_output.txt`. The two commands create `lean/.lake/` (about 5 GB), which `.gitignore` excludes and which can be deleted after the check.

## Where each result comes from

| In the article or the Supplementary Material | Output |
|---|---|
| Section 5.2, Table S5, Figure S1 (calibration checks) | `out/cc2_calibration_checks.json`, `data/derived/data_stats.json`, `out/pix_impediments.json` |
| Section 5.1 (votes and transfers), Section S7.2, Figure S6 | `out/electoral_connection.json`, `data/derived/tse_summary.json` |
| Table 3, Tables S6, S7 | `out/cc2_worlds.npz`, `out/cc2_numbers.json` |
| Numbers in Sections 1 and 6 that are not in a table | `out/cc2_text_numbers.json` (written by `code/cc2_textnums.py`) |
| Table S2 (propositions) | `out/cc2_props.json` |
| Propositions 1–7 and Supplementary Propositions 8–9 (formal proofs) | `lean/ChapecoProofs/` (proofs), `lean/results/lake_build_output.txt` (output of `lake build`) |
| Table S8 (robustness) | `out/cc2_robust.json` |
| Table S9, Figures 10a and S4 (sensitivity) | `out/cc2_gsa_R0.json`, `out/cc2_gsa_R15.json` |
| Scenario discovery (Section 6.8, Section S6.2, Figure 10b–c) | `out/cc2_discovery.json` |
| Table S10, Figures 4a and S5 (real colleges) | `out/real_colleges.json`, `out/college_expected.json` |
| Figure S3 (national accounting) | `out/national_accounting.json` |

## Figure files

| Figure | File in `figs/` | Name of the figure file submitted with the article |
|---|---|---|
| 1 | `fig1_sc` | `fig1_santa_catarina` |
| 2 | `fig2_cycle` | `fig2_model` |
| 3 | `fig4_chamber` | `fig3_chamber` |
| 4 | `fig5_control` | `fig4_control` |
| 5 | `fig3_statusquo` | `fig5_status_quo` |
| 6 | `fig7_value` | `fig6_value` |
| 7 | `fig6_cooperation` | `fig7_cooperation` |
| 8 | `fig8_sanctions` | `fig8_sanctions` |
| 9 | `fig9_designs` | `fig9_designs` |
| 10 | `fig10_discovery` | `fig10_drivers` |
| S1 | `figS2_calibration` | `figS1_calibration` |
| S2 | `figS4_losers` | `figS2_value_change_map` |
| S3 | `fig11_national` | `figS3_national` |
| S4 | `figS3_morris` | `figS4_morris` |
| S5 | `figS1_banzhaf` | `figS5_banzhaf` |
| S6 | `figS6_electoral` | `figS6_electoral` |

## Conventions

- Money is in reais per year at 2025 values; the money of every design is the same, R$ 595.2 million a year (16 deputies × R$ 37.2 million).
- Results are medians across the 2,000 worlds, with 5th and 95th percentiles, unless stated otherwise. Shares of worlds count a design as better than another when it exceeds it by more than a relative tolerance of 1e-9.
- Design codes (SQ, CL, L0, D0, R0–R16) are the same in the code and in the text (Table 2).
- The votes for federal deputy come from the TSE open-data repository (files generated on 8 October 2026; Supplementary Material 04, Section S4.1); the sources of the other data are given in Supplementary Material 04 – Data and Calibration (Section S4.1 and Table S3).
