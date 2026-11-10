/-
Proposition 3 (cooperation), Supplementary Material 03, Section S3.3.

Given the plan and the other mayors' choices, mayor `m` co-finances project `k` with probability
`Λ(NG/(ς stake))`, where

  `NG = (1 + γ̃) w V (Δq + ε_x q) + δ F - stake`

is the net gain from cooperating. Cooperation is more likely than not if and only if `δ > δ*`, with
`δ* = (stake - (1 + γ̃) w V (Δq + ε_x q))/F`.

What is formalized here: the probability of cooperation when the cost shock has a logistic
distribution (`prob_cooperate`, with `exists_logistic_distribution` showing that such a
distribution exists), the threshold (`netGain_pos_iff`, `proposition3`), the comparative statics,
and the corollary on small participants (`hasDerivAt_completionGain`,
`completionGain_taylor`, `benefit_isBigO_sq`, `benefit_over_stake_tendsto_zero`).

Not formalized: the existence of an equilibrium of the cooperation game, which the supplement
derives from Brouwer's fixed-point theorem; Mathlib does not contain Brouwer's theorem.
-/
import ChapecoProofs.Basic

noncomputable section

open Real Filter Topology MeasureTheory ProbabilityTheory Asymptotics

namespace Chapeco.P3

/-! ## The net gain and the threshold -/

/-- The mayor's net gain from cooperating, `NG = (1 + γ̃) w V (Δq + ε_x q) + δ F - stake`. -/
def netGain (γ w V Δq εx q δ F stake : ℝ) : ℝ :=
  (1 + γ) * w * V * (Δq + εx * q) + δ * F - stake

/-- The threshold `δ* = (stake - (1 + γ̃) w V (Δq + ε_x q))/F`. -/
def threshold (γ w V Δq εx q F stake : ℝ) : ℝ :=
  (stake - (1 + γ) * w * V * (Δq + εx * q)) / F

/-- **Step 2 (the threshold).** With `F > 0`, `NG > 0` if and only if `δ > δ*`. -/
theorem netGain_pos_iff {γ w V Δq εx q δ F stake : ℝ} (hF : 0 < F) :
    0 < netGain γ w V Δq εx q δ F stake ↔ threshold γ w V Δq εx q F stake < δ := by
  unfold netGain threshold
  rw [div_lt_iff₀ hF]
  constructor <;> intro h <;> linarith

/-! ## The probability of cooperation -/

/-- A probability measure on `ℝ` with a continuous distribution function has no atoms. -/
theorem noAtoms_of_continuous_cdf (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h : Continuous (cdf ν)) : NoAtoms ν := by
  refine ⟨fun a => ?_⟩
  rw [← measure_cdf ν, StieltjesFunction.measure_singleton,
    leftLim_eq_of_tendsto (nhdsLT_neBot a).ne ((h.tendsto a).mono_left nhdsWithin_le_nhds),
    sub_self, ENNReal.ofReal_zero]

/-- **Step 2 (the probability).** If the cost shock `ε` has the logistic distribution with scale
`sc` (its distribution function is `x ↦ Λ(x/sc)`), the mayor, who cooperates if `NG + ε ≥ 0`,
cooperates with probability `Λ(NG/sc)`. -/
theorem prob_cooperate (ν : Measure ℝ) [IsProbabilityMeasure ν] {sc : ℝ}
    (hν : ∀ x, cdf ν x = logistic (x / sc)) (NG : ℝ) :
    ν.real {ε | 0 ≤ NG + ε} = logistic (NG / sc) := by
  have hfun : ⇑(cdf ν) = fun x => logistic (x / sc) := funext hν
  have hcont : Continuous (cdf ν) := by
    rw [hfun]
    exact logistic_continuous.comp (continuous_id.div_const sc)
  haveI := noAtoms_of_continuous_cdf ν hcont
  have hset : {ε : ℝ | 0 ≤ NG + ε} = (Set.Iio (-NG))ᶜ := by
    ext ε
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_Iio, not_lt]
    constructor <;> intro h <;> linarith
  rw [hset, measureReal_compl measurableSet_Iio, measureReal_univ_eq_one,
    measureReal_congr (Iio_ae_eq_Iic (μ := ν) (a := -NG)), ← cdf_eq_real (μ := ν), hν, neg_div,
    one_sub_logistic_neg]

/-- The hypothesis on the cost shock is satisfiable: for every scale `sc > 0` there is a probability
measure on `ℝ` whose distribution function is `x ↦ Λ(x/sc)` (the logistic distribution). -/
theorem exists_logistic_distribution {sc : ℝ} (hsc : 0 < sc) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ∀ x, cdf ν x = logistic (x / sc) := by
  have hcont : Continuous fun x : ℝ => logistic (x / sc) :=
    logistic_continuous.comp (continuous_id.div_const sc)
  let F : StieltjesFunction :=
    { toFun := fun x => logistic (x / sc)
      mono' := fun a b hab => logistic_strictMono.monotone (div_le_div_of_nonneg_right hab hsc.le)
      right_continuous' := fun x => hcont.continuousAt.continuousWithinAt }
  have h0 : Tendsto F atBot (𝓝 0) :=
    tendsto_logistic_atBot.comp (tendsto_id.atBot_div_const hsc)
  have h1 : Tendsto F atTop (𝓝 1) :=
    tendsto_logistic_atTop.comp (tendsto_id.atTop_div_const hsc)
  refine ⟨F.measure, F.isProbabilityMeasure h0 h1, fun x => ?_⟩
  rw [cdf_measure_stieltjesFunction F h0 h1]

/-- Cooperation is more likely than not if and only if the net gain is positive. -/
theorem half_lt_prob_iff {sc : ℝ} (hsc : 0 < sc) (NG : ℝ) :
    1 / 2 < logistic (NG / sc) ↔ 0 < NG := by
  rw [half_lt_logistic_iff, div_pos_iff_of_pos_right hsc]

/-- **Proposition 3.** With a logistic cost shock of scale `ς · stake`, the mayor cooperates with
probability `Λ(NG/(ς stake))`, and cooperation is more likely than not if and only if `δ > δ*`. -/
theorem proposition3 (ν : Measure ℝ) [IsProbabilityMeasure ν] {ς stake : ℝ} (hς : 0 < ς)
    (hstake : 0 < stake) (hν : ∀ x, cdf ν x = logistic (x / (ς * stake)))
    {γ w V Δq εx q δ F : ℝ} (hF : 0 < F) :
    ν.real {ε | 0 ≤ netGain γ w V Δq εx q δ F stake + ε} =
        logistic (netGain γ w V Δq εx q δ F stake / (ς * stake)) ∧
      (1 / 2 < ν.real {ε | 0 ≤ netGain γ w V Δq εx q δ F stake + ε} ↔
        threshold γ w V Δq εx q F stake < δ) := by
  have h := prob_cooperate ν hν (netGain γ w V Δq εx q δ F stake)
  refine ⟨h, ?_⟩
  rw [h, half_lt_prob_iff (mul_pos hς hstake), netGain_pos_iff hF]

/-! ## Comparative statics -/

section ComparativeStatics

variable {γ w V Δq εx q δ F stake : ℝ}

theorem netGain_strictMono_εx (h : 0 < (1 + γ) * w * V * q) :
    StrictMono fun εx => netGain γ w V Δq εx q δ F stake := by
  intro a b hab
  simp only [netGain]
  nlinarith [mul_lt_mul_of_pos_left hab h]

theorem netGain_strictMono_δ (hF : 0 < F) :
    StrictMono fun δ => netGain γ w V Δq εx q δ F stake := by
  intro a b hab
  simp only [netGain]
  nlinarith [mul_lt_mul_of_pos_right hab hF]

theorem netGain_strictMono_F (hδ : 0 < δ) :
    StrictMono fun F => netGain γ w V Δq εx q δ F stake := by
  intro a b hab
  simp only [netGain]
  nlinarith [mul_lt_mul_of_pos_left hab hδ]

theorem netGain_strictMono_γ (h : 0 < w * V * (Δq + εx * q)) :
    StrictMono fun γ => netGain γ w V Δq εx q δ F stake := by
  intro a b hab
  simp only [netGain]
  nlinarith [mul_lt_mul_of_pos_right hab h]

theorem netGain_strictMono_V (h : 0 < (1 + γ) * w * (Δq + εx * q)) :
    StrictMono fun V => netGain γ w V Δq εx q δ F stake := by
  intro a b hab
  simp only [netGain]
  nlinarith [mul_lt_mul_of_pos_left hab h]

theorem netGain_strictAnti_stake : StrictAnti fun stake => netGain γ w V Δq εx q δ F stake := by
  intro a b hab
  simp only [netGain]
  linarith

/-- The stake: the co-financing share valued at `1 + ℓ` per real plus the host's local cost. -/
def stakeOf (ℓ χ C wt localCost : ℝ) : ℝ := (1 + ℓ) * χ * C * wt + localCost

theorem netGain_strictAnti_ℓ {χ C wt localCost : ℝ} (h : 0 < χ * C * wt) :
    StrictAnti fun ℓ => netGain γ w V Δq εx q δ F (stakeOf ℓ χ C wt localCost) := by
  intro a b hab
  simp only [netGain, stakeOf]
  nlinarith [mul_lt_mul_of_pos_right hab h]

/-- The horizon `δ = β⁴ π^stay π^cont` is zero for term-limited mayors (`π^stay = 0`). -/
theorem horizon_term_limited (β πcont : ℝ) : β ^ 4 * 0 * πcont = 0 := by
  ring

/-- The continuity term `π^cont = p^next [f + κ_P (1 - f)]`. -/
def continuity (pnext κP f : ℝ) : ℝ := pnext * (f + κP * (1 - f))

/-- With `κ_P < 1`, continuity increases with the probability `f` that the incumbent may stay. -/
theorem continuity_strictMono {pnext κP : ℝ} (hp : 0 < pnext) (hκ : κP < 1) :
    StrictMono (continuity pnext κP) := by
  intro a b hab
  unfold continuity
  have : 0 < (1 - κP) * (b - a) := mul_pos (by linarith) (by linarith)
  nlinarith [mul_pos hp this]

/-- A single term (`f = 0`) gives less continuity than the bar (`f = f_j`), which gives less than no
bar (`f = 1`), when `κ_P < 1` and `0 < f_j < 1`. -/
theorem continuity_single_lt_bar_lt_nobar {pnext κP fj : ℝ} (hp : 0 < pnext) (hκ : κP < 1)
    (h0 : 0 < fj) (h1 : fj < 1) :
    continuity pnext κP 0 < continuity pnext κP fj ∧
      continuity pnext κP fj < continuity pnext κP 1 :=
  ⟨continuity_strictMono hp hκ h0, continuity_strictMono hp hκ h1⟩

end ComparativeStatics

/-! ## Corollary: small participants -/

/-- The completion gain bought by a participant with share `w`:
`Δq(w) = Q H [(c + χ w)^ν - c^ν]`, where `c` is the funded share without the participant. -/
def completionGain (Q H c χ ν w : ℝ) : ℝ := Q * H * ((c + χ * w) ^ ν - c ^ ν)

theorem hasDerivAt_completionGain_at {Q H c χ ν w : ℝ} (hw : 0 < c + χ * w) :
    HasDerivAt (completionGain Q H c χ ν) (Q * H * ν * (c + χ * w) ^ (ν - 1) * χ) w := by
  have h1 : HasDerivAt (fun y => c + χ * y) (χ * 1) w :=
    ((hasDerivAt_id' w).const_mul χ).const_add c
  have h2 := ((h1.rpow_const (p := ν) (Or.inl hw.ne')).sub_const (c ^ ν)).const_mul (Q * H)
  show HasDerivAt (fun y => Q * H * ((c + χ * y) ^ ν - c ^ ν)) _ w
  refine h2.congr_deriv ?_
  ring

/-- **Corollary (first order).** `Δq'(0) = Q H ν c^{ν-1} χ`. -/
theorem hasDerivAt_completionGain {Q H c χ ν : ℝ} (hc : 0 < c) :
    HasDerivAt (completionGain Q H c χ ν) (Q * H * ν * c ^ (ν - 1) * χ) 0 := by
  have h := hasDerivAt_completionGain_at (Q := Q) (H := H) (ν := ν) (w := 0)
    (show 0 < c + χ * 0 by rw [mul_zero, add_zero]; exact hc)
  rwa [mul_zero, add_zero] at h

theorem completionGain_zero (Q H c χ ν : ℝ) : completionGain Q H c χ ν 0 = 0 := by
  unfold completionGain
  simp

/-- **Corollary, equation of `Δq`.**
`Δq(w) = Q H ν c^{ν-1} χ w + O(w²)` as the participant's share `w` goes to zero. -/
theorem completionGain_taylor {Q H c χ ν : ℝ} (hc : 0 < c) :
    (fun w => completionGain Q H c χ ν w - Q * H * ν * c ^ (ν - 1) * χ * w) =O[𝓝 0]
      fun w => w ^ 2 := by
  have hpos : ∀ᶠ w in 𝓝 (0 : ℝ), 0 < c + χ * w := by
    have hcont : Continuous fun w : ℝ => c + χ * w := by fun_prop
    have h0 : 0 < c + χ * 0 := by rw [mul_zero, add_zero]; exact hc
    exact Filter.Tendsto.eventually hcont.continuousAt (lt_mem_nhds h0)
  have hf : ∀ᶠ w in 𝓝 (0 : ℝ), HasDerivAt (completionGain Q H c χ ν)
      ((fun w => Q * H * ν * (c + χ * w) ^ (ν - 1) * χ) w) w := by
    filter_upwards [hpos] with w hw
    exact hasDerivAt_completionGain_at hw
  have hdiff : DifferentiableAt ℝ (fun w => Q * H * ν * (c + χ * w) ^ (ν - 1) * χ) 0 := by
    have h1 : HasDerivAt (fun y => c + χ * y) (χ * 1) 0 :=
      ((hasDerivAt_id' 0).const_mul χ).const_add c
    have h0 : c + χ * 0 ≠ 0 := by rw [mul_zero, add_zero]; exact hc.ne'
    exact ((h1.rpow_const (p := ν - 1) (Or.inl h0)).differentiableAt.const_mul
      (Q * H * ν)).mul_const χ
  refine (isBigO_sub_sub_deriv hf hdiff).congr (fun w => ?_) (fun w => ?_)
  · simp only [completionGain_zero, sub_zero, mul_zero, add_zero]
  · simp only [sub_zero]

/-- The benefit of completion for a participant whose benefit weight is proportional to its share,
`ω₀ w V Δq(w)`, is second order in the share. -/
theorem benefit_isBigO_sq {Q H c χ ν ω₀ V : ℝ} (hc : 0 < c) :
    (fun w => ω₀ * w * V * completionGain Q H c χ ν w) =O[𝓝 0] fun w => w ^ 2 := by
  have h1 : (fun w : ℝ => ω₀ * w * V) =O[𝓝 0] fun w => w :=
    ((isBigO_refl (fun w : ℝ => w) (𝓝 0)).const_mul_left (ω₀ * V)).congr_left fun w => by
      show ω₀ * V * w = ω₀ * w * V
      ring
  have h2 : (completionGain Q H c χ ν) =O[𝓝 0] fun w => w := by
    have h :=
      (hasDerivAt_completionGain (Q := Q) (H := H) (χ := χ) (ν := ν) hc).hasFDerivAt.isBigO_sub
    simpa [completionGain_zero] using h
  refine (h1.mul h2).congr (fun w => ?_) (fun w => ?_)
  · ring
  · ring

/-- **Corollary.** The stake of a participant with share `w` is `κ w`, with
`κ = (1 + ℓ) χ_cof C ≠ 0`. The ratio of the benefit that its payment buys through completion to the
stake vanishes as the share goes to zero, so for small participants the sign of `NG` is decided by
the enforcement terms against the stake. -/
theorem benefit_over_stake_tendsto_zero {Q H c χ ν ω₀ V κ : ℝ} (hc : 0 < c) (hκ : κ ≠ 0) :
    Tendsto (fun w => ω₀ * w * V * completionGain Q H c χ ν w / (κ * w)) (𝓝[≠] 0) (𝓝 0) := by
  have hcont : Tendsto (completionGain Q H c χ ν) (𝓝[≠] 0) (𝓝 0) := by
    have h := (hasDerivAt_completionGain (Q := Q) (H := H) (χ := χ) (ν := ν) hc).continuousAt
    rw [ContinuousAt, completionGain_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hlim := hcont.const_mul (ω₀ * V / κ)
  rw [mul_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw' : w ≠ 0 := hw
  field_simp
  ring

end Chapeco.P3
