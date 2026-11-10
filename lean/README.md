# Formal verification of the propositions (Lean 4 and Mathlib)

This folder contains machine-checked proofs, written in Lean 4 with the Mathlib library, of the mathematical statements of Propositions 1–7 and Supplementary Propositions 8–9 of Supplementary Material 03 ("Proofs and Numerical Checks"). Lean accepts a proof only if every step follows from the definitions, from the stated hypotheses and from results already proved in Mathlib, so a successful build certifies the theorems listed below. The numerical results of the article (simulations, calibration, Table S2) are not part of this verification; they are reproduced by the Python code of the replication package.

## How to build

1. Install `elan`, the Lean version manager (https://lean-lang.org/install or https://github.com/leanprover/elan). It reads the file `lean-toolchain` and installs Lean `v4.20.0` automatically.
2. In this folder, download the compiled Mathlib library and build the proofs:

```
lake exe cache get
lake build
```

With the downloaded library, the build takes a few minutes. Without it, Lake compiles the parts of Mathlib that the proofs use, which takes several hours. The two commands create the folder `.lake/` (about 5 GB: the compiled Mathlib library and the compiled proofs). It is not part of the package, `.gitignore` excludes it, and it can be deleted after the check; `lake exe cache get` recreates it.

A successful build ends with the message of the audit module, `ChapecoProofs/Audit.lean`:

```
177 declarations in the Chapeco namespace checked: none uses sorry, and none depends on an axiom other than propext, Classical.choice and Quot.sound.
```

The audit inspects every declaration of the project and makes the build fail if any proof is incomplete (`sorry`) or depends on an axiom other than the three standard axioms on which Mathlib itself rests. The same module prints the axioms of the main theorem of each proposition (`#print axioms`).

Versions: Lean `v4.20.0`, Mathlib `v4.20.0` (commit `c211948581bde9846a99e32d97a03f0d5307c31e`), fixed in `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`.

## Results

`results/lake_build_output.txt` is the output of the two commands on Windows (PowerShell), on 9 October 2026: the 6,772 files of the compiled Mathlib library were downloaded, the build completed, and the audit checked 177 declarations, none of which uses `sorry` or an axiom other than the three standard ones. The axioms of the main theorem of each proposition follow in the same file. A build of the same files on Linux gave the same result.

## Files

| File | Content |
|---|---|
| `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` | Lean version, project definition and the pinned versions of Mathlib and its dependencies |
| `ChapecoProofs.lean` | Root of the library: imports every file below |
| `ChapecoProofs/Imports.lean` | The parts of Mathlib used by the proofs |
| `ChapecoProofs/Basic.lean` | Logistic function `Λ`; standard normal density `φ` and distribution function `Φ` (defined from Mathlib's Gaussian measure `gaussianReal 0 1`, with `Φ' = φ` proved); a second-order remainder estimate |
| `ChapecoProofs/P1Selection.lean` | Proposition 1 (selection) |
| `ChapecoProofs/P2Effort.lean` | Proposition 2 (effort and relocation) |
| `ChapecoProofs/P3Cooperation.lean` | Proposition 3 (cooperation) and its corollary on small participants |
| `ChapecoProofs/P4Hurdle.lean` | Proposition 4 (completion hurdle) |
| `ChapecoProofs/P5CrowdingOut.lean` | Proposition 5 (effort and crowding out) |
| `ChapecoProofs/P6Tilt.lean` | Proposition 6 (pre-election tilt) |
| `ChapecoProofs/P7SanctionTrap.lean` | Proposition 7 (the sanction trap) |
| `ChapecoProofs/SP8Sanctions.lean` | Supplementary Proposition 8 (credibility of territorial sanctions) |
| `ChapecoProofs/SP9Inspection.lean` | Supplementary Proposition 9 (inspection) |
| `ChapecoProofs/Audit.lean` | Audit of `sorry` and axioms |
| `results/lake_build_output.txt` | Output of `lake exe cache get` and `lake build` (see Results) |

## Correspondence between the supplement and the Lean theorems

Each row gives the statement or step of Supplementary Material 03, the Lean theorem or theorems that prove it, and the file. Equation numbers are those of the Supplementary Material.

| Supplement | Lean theorem | File |
|---|---|---|
| **Proposition 1 (selection)** | | `P1Selection.lean` |
| Step 1: the index has variance `D = 1 + t² + 2tρ + s²` and covariance `1 + tρ` with legislative skill (`t + ρ` with brokerage skill) | `var_index`, `cov_skill_index`, `cov_brokerage_index` | |
| Step 1: `E[λ_L ∣ I] = r(t,s) Ĩ`, equations (S12)–(S13) | `condExp_eq_projection`, `projection_coeff` | |
| Step 2: `E[λ_L ∣ elected] = r(t,s) a(S,N)`, equations (S11) and (S14), for any selection rule that depends only on the indices | `expected_skill_elected`, `expected_mean_skill_elected` | |
| Step 2: `E[λ_B ∣ elected] = r_B a(S,N)` | `expected_brokerage_elected` | |
| Step 2: `a(S,N)` is the same under both list rules | `selection_mean_invariant` | |
| Step 3: `∂r/∂t = D^{-3/2}[ρs² − t(1 − ρ²)]`, equation (S15) | `hasDerivAt_corr` | |
| `r` falls with `t` if and only if `t > ρs²/(1 − ρ²)` | `deriv_corr_neg_iff`, `deriv_corr_pos_iff`, `corr_strictAntiOn`, `corr_strictMonoOn` | |
| Step 4: closed lists raise the expected skill of the elected if and only if `r(Xt₀, σ_ν) > r(t₀, σ_ε)` | `closed_lists_raise_skill_iff` | |
| **Proposition 2 (effort and relocation)** | | `P2Effort.lean` |
| Step 1: `e = W_B/(W_B + W_L)` is the unique maximizer of `W_B ln e + W_L ln(1 − e)`; `W_L = W_B(1 − s₀)/s₀` | `careerValue_le`, `careerValue_lt`, `weight_ratio` | |
| Step 2: `e_B = X s₀/(X s₀ + 1 − s₀)`, `X = πψ/κ`, equations (S16)–(S18) | `effort_after_reform`, `proposition2_effort` | |
| Step 3: `e_B` increases with `X` and equals `s₀` at `X = 1`; legislative effort rises if and only if `X < 1` | `brokerShare_strictMonoOn`, `brokerShare_one`, `legislative_effort_rises_iff` | |
| Step 4: `ψ = 1` if `η = 1`; `ψ` and the brokerage share increase with `s̄` if `η < 1` and `χ > 0` | `psi_of_eta_one`, `psi_strictMono`, `brokerage_increasing_in_county_money` | |
| **Proposition 3 (cooperation)** | | `P3Cooperation.lean` |
| Step 2: with a logistic cost shock of scale `ς·stake`, the mayor cooperates with probability `Λ(NG/(ς·stake))`, with `NG` as in equation (S19) | `prob_cooperate`, `proposition3` | |
| The logistic distribution of the cost shock exists | `exists_logistic_distribution` | |
| Step 2: cooperation is more likely than not if and only if `NG > 0`, that is, `δ > δ*`, equation (S20) | `half_lt_prob_iff`, `netGain_pos_iff`, `proposition3` | |
| Comparative statics in `ε_x`, `δ`, `F`, `γ̃`, `V`, the stake and `ℓ`; `δ = 0` for term-limited mayors; continuity is lowest with a single term and highest without the bar | `netGain_strictMono_εx`, `netGain_strictMono_δ`, `netGain_strictMono_F`, `netGain_strictMono_γ`, `netGain_strictMono_V`, `netGain_strictAnti_stake`, `netGain_strictAnti_ℓ`, `horizon_term_limited`, `continuity_strictMono`, `continuity_single_lt_bar_lt_nobar` | |
| Corollary: `Δq = Q H ν c^{ν−1} χ w̃ + O(w̃²)`, equation (S21) | `hasDerivAt_completionGain`, `completionGain_taylor` | |
| Corollary: the benefit bought through completion is second order in the share, the stake first order | `benefit_isBigO_sq`, `benefit_over_stake_tendsto_zero` | |
| **Proposition 4 (completion hurdle)** | | `P4Hurdle.lean` |
| Steps 1–2: the inclusion rule (S23)–(S24) collects into (S25), with `q_eff` and `s_w` as in (S26)–(S27) | `social_value_collect` | |
| Step 3: the rule holds if and only if `σ > σ*(q)`, equation (S22) | `include_iff_hurdle` | |
| Step 4: `∂q_eff/∂q > 0` and `∂s_w/∂q < 0`, equations (S28)–(S29) | `hasDerivAt_qEff`, `deriv_qEff_pos`, `hasDerivAt_sW`, `deriv_sW_neg` | |
| Step 4: the hurdle falls with `q` if and only if condition (S30) holds; without salvage value it always falls | `hasDerivAt_hurdle`, `hurdle_deriv_neg_iff`, `hurdle_strictAntiOn_no_salvage` | |
| **Proposition 5 (effort and crowding out)** | | `P5CrowdingOut.lean` |
| (i) `e_u*`, equations (S31) and (S33), is the unique maximizer; `∂e_u*/∂e_m = −1` while `e_u* > 0` | `objective_le`, `objective_lt`, `total_effort`, `hasDerivAt_unmeasuredEffort` | |
| (ii) the derivative of (S34) is the motive (S32) | `hasDerivAt_reappointment` (with `hasDerivAt_normalCDF`, `Basic.lean`) | |
| (ii) the motive is strongest at the threshold and vanishes far above or below it | `motiveFactor_le`, `motiveFactor_lt`, `tendsto_motiveFactor_atTop`, `tendsto_motiveFactor_atBot` | |
| (iii) with one vote per mayor, the mean of the mayors' gains, each with weight `1/n_j` | `oneVoteMean_eq` | |
| **Proposition 6 (pre-election tilt)** | | `P6Tilt.lean` |
| Step 3: the water-filling tilt (S35) is the unique optimum of the objective built from (S37), municipality by municipality and for the conde's whole problem | `tiltGain_le`, `tiltGain_lt`, `total_tiltGain_le` | |
| Step 3: Kuhn–Tucker condition `A_m/(h_V Rev_m + T_m) = λ` where `T_m > 0` | `kkt` | |
| Step 4: for `p` as in (S36), at `T = 0`, `∂p/∂T = p(1 − p)α_V/Rev`; the price of one more expected co-partisan mayor is `Rev/[p(1 − p)α_V]` | `hasDerivAt_winProb`, `price_of_control` | |
| **Proposition 7 (the sanction trap)** | | `P7SanctionTrap.lean` |
| (i) without the bar, the map (S38) is constant and the steady state is unique | `no_bar_constant`, `no_bar_unique_steady_state` | |
| (ii) with the bar and `κ_P < 1`, `Γ` lies below its no-bar value for every `c` | `bar_lowers_map`, `bar_lowers_map_normal` | |
| Step 3: `Γ` is continuous and increasing, `Γ(0) > 0`, `Γ(1) < 1`, and has a steady state | `completionMap_continuous`, `completionMap_monotone`, `completionMap_pos`, `completionMap_lt_one`, `exists_steady_state` | |
| (iii) a crossing of the diagonal from below at `ĉ` implies a steady state on each side of `ĉ` | `three_steady_states`, `sanction_trap` | |
| Step 4: with `Π` as in (S39), `Γ` increases with the county's capacity relative to the threshold, and `Π` is close to zero in low-capacity counties | `completionMap_mono_capacity`, `passProb_monotone`, `passProb_tendsto_zero` | |
| **Supplementary Proposition 8** | | `SP8Sanctions.lean` |
| `Pr(U[0, Ξ] > n^ϱ) = (1 − n^ϱ/Ξ)⁺`, equation (S40), which falls with need when `ϱ > 0` | `prob_gt`, `supplementary_proposition8`, `enforceProb_antitoneOn`, `enforceProb_strictAntiOn` | |
| **Supplementary Proposition 9** | | `SP9Inspection.lean` |
| Expected return `1 − p_I(1 + s_D)`; share attempted `[1 − p_I(1 + s_D)]⁺`; factor (S41), equal to one without inspection | `expected_return`, `prob_lt`, `supplementary_proposition9`, `inspectionFactor_zero` | |
| **Common functions** | | `Basic.lean` |
| Logistic function `Λ` and its properties; `Λ' = Λ(1 − Λ)` | `hasDerivAt_logistic`, `logistic_strictMono`, `one_sub_logistic_neg`, `half_lt_logistic_iff` | |
| Normal distribution function `Φ` (from Mathlib's Gaussian measure) and density `φ`: `Φ' = φ`; `φ` largest at zero and vanishing in the tails | `hasDerivAt_normalCDF`, `normalCDF_strictMono`, `normalCDF_lt_one`, `stdNormalPDF_eq_gaussianPDFReal`, `stdNormalPDF_lt_zero`, `tendsto_stdNormalPDF_atTop` | |

## What is taken as a hypothesis or left out

The formalization proves each statement from the assumptions of the model. Where the supplement relies on a result that Mathlib does not contain, or where a step defines the model rather than derives a result, the Lean files say so, and the list below summarizes these points.

1. **Proposition 1.** The moments of the skills and of the noise (means zero, unit variances, correlation `ρ`, noise uncorrelated with the skills) are hypotheses, as in the statement. Mathlib does not yet contain the multivariate normal distribution, so the one consequence of joint normality that the proof uses enters as a hypothesis: the residual of skill after its linear projection on the index, `λ_L − (Cov(λ_L, I)/Var(I)) I`, is independent of the σ-algebra generated by the indices of all aspirants (for jointly normal variables, a residual uncorrelated with the indices is independent of them). From this hypothesis the conditional mean `E[λ_L ∣ I] = r(t,s) Ĩ` is proved, not assumed. The same hypothesis, for brokerage skill, gives `E[λ_B ∣ elected] = r_B a(S,N)`. The selection rule is any rule that depends only on the indices, which includes the election of the `S` highest-ranked aspirants.
2. **Proposition 3.** The cost shock is represented by its distribution function, `x ↦ Λ(x/(ς·stake))`; that such a distribution exists is proved (`exists_logistic_distribution`). Step 1 of the proof, the accounting that adds up the three parts of the net gain (including the approximation that values the loss from exclusion at `q`), defines `NG` and is the definition `netGain`. The existence of an equilibrium of the cooperation game, which the supplement obtains from Brouwer's fixed-point theorem, is not formalized, because Mathlib does not contain Brouwer's theorem.
3. **Proposition 5 (iii)** and **Proposition 6, Step 2** (the linearization of `Λ` around the status quo, which defines the conde's objective) are definitions of the model; the files state them as definitions and prove the results that follow from them.
4. **Proposition 7.** The crossing of the diagonal from below is a hypothesis (`Γ(ĉ) = ĉ` and `Γ'(ĉ) > 1`), as in the statement. The local stability of the steady states (`Γ' < 1` at a crossing) and the numerical example (three steady states for capacities in `[−3.5, −1.15]`) are not formalized.
5. The numerical checks of Table S2 and all simulation results of the article are outside the formalization.

The formalization also made three conditions explicit that the text leaves implicit: the derivative of the salvage term in Proposition 4 is negative for `q < 1` (at `q = 1` it equals `−v_inc ā`, which is zero when `ā = 0`); the Kuhn–Tucker condition of Proposition 6 uses `h_V Rev_m > 0`; and Step 4 of Proposition 1 uses `a(S,N) > 0`, which holds when `S < N`. None of them changes a result of the article.

## Notation

Lean identifiers cannot use some of the symbols of the supplement. The correspondence is: `piB` for the multiplier `π` of Proposition 2 (`π` denotes the number pi in Mathlib), `lam` for `λ`, `Pass` for `Π`, `cap` for capacity `μ` in Proposition 7, `corr` for `r(t, s)`, `D` for the variance of the index, `corrB` for `r_B`, `ch` for the crossing point `ĉ` of Proposition 7, `ς` for the scale of the cost shock, `Ξ` and `ϱ` as in the supplement. Each file begins with a short description of its variables.
