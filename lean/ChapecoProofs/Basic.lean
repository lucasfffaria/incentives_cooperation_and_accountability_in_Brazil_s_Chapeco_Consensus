/-
Formal verification of the propositions of Supplementary Material 03 of "Separating the legislator
from the broker: incentives, cooperation and accountability in Brazil's 'Chapecó Consensus'".

This file collects the functions and results used by several propositions:

* the logistic function `Λ`, which gives the probability of cooperation (Proposition 3), the
  probability that the conde's party wins a municipality (Proposition 6) and the completion map
  (Proposition 7);
* the standard normal density `φ` and distribution function `Φ`, which give the reappointment
  motive (Proposition 5) and the probability of meeting the target (Proposition 7). `Φ` is defined
  as the distribution function of Mathlib's standard Gaussian measure `gaussianReal 0 1`, and its
  derivative is proved to be `φ`;
* a second-order remainder estimate, used in the corollary of Proposition 3.
-/
import ChapecoProofs.Imports

noncomputable section

open Real Filter Topology MeasureTheory ProbabilityTheory

namespace Chapeco

/-! ## The logistic function -/

/-- The logistic function `Λ(z) = 1 / (1 + e^{-z})`. -/
def logistic (z : ℝ) : ℝ := 1 / (1 + Real.exp (-z))

theorem logistic_pos (z : ℝ) : 0 < logistic z := by
  unfold logistic
  positivity

theorem logistic_lt_one (z : ℝ) : logistic z < 1 := by
  unfold logistic
  rw [div_lt_one (by positivity)]
  linarith [Real.exp_pos (-z)]

theorem logistic_zero : logistic 0 = 1 / 2 := by
  unfold logistic
  norm_num

/-- The logistic function is strictly increasing. -/
theorem logistic_strictMono : StrictMono logistic := by
  intro a b hab
  unfold logistic
  apply one_div_lt_one_div_of_lt (by positivity)
  have : Real.exp (-b) < Real.exp (-a) := Real.exp_lt_exp.mpr (by linarith)
  linarith

theorem logistic_lt_logistic_iff {a b : ℝ} : logistic a < logistic b ↔ a < b :=
  logistic_strictMono.lt_iff_lt

/-- `Λ(z) > 1/2` if and only if `z > 0`. -/
theorem half_lt_logistic_iff (z : ℝ) : 1 / 2 < logistic z ↔ 0 < z := by
  rw [← logistic_zero]
  exact logistic_strictMono.lt_iff_lt

/-- Symmetry of the logistic distribution: `1 - Λ(-z) = Λ(z)`. -/
theorem one_sub_logistic_neg (z : ℝ) : 1 - logistic (-z) = logistic z := by
  unfold logistic
  rw [neg_neg, Real.exp_neg]
  have hz : 0 < Real.exp z := Real.exp_pos z
  field_simp
  ring

/-- The derivative of the logistic function: `Λ' = Λ (1 - Λ)`. -/
theorem hasDerivAt_logistic (z : ℝ) :
    HasDerivAt logistic (logistic z * (1 - logistic z)) z := by
  have h1 : HasDerivAt (fun y => 1 + Real.exp (-y)) (-Real.exp (-z)) z := by
    have h := ((Real.hasDerivAt_exp (-z)).comp z (hasDerivAt_neg z)).const_add 1
    simpa using h
  have hne : (1 + Real.exp (-z)) ≠ 0 := by positivity
  have h2 := h1.inv hne
  have heq : (fun y => (1 + Real.exp (-y))⁻¹) = logistic := by
    funext y
    simp [logistic]
  rw [heq] at h2
  convert h2 using 1
  unfold logistic
  have hpos : 0 < 1 + Real.exp (-z) := by positivity
  field_simp
  ring

theorem logistic_continuous : Continuous logistic :=
  continuous_iff_continuousAt.2 fun z => (hasDerivAt_logistic z).continuousAt

theorem tendsto_logistic_atTop : Tendsto logistic atTop (𝓝 1) := by
  have h : Tendsto (fun z => 1 / (1 + Real.exp (-z))) atTop (𝓝 (1 / (1 + 0))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.add Real.tendsto_exp_neg_atTop_nhds_zero)
      (by norm_num)
  have h1 : (1 : ℝ) / (1 + 0) = 1 := by norm_num
  rw [h1] at h
  exact h

theorem tendsto_logistic_atBot : Tendsto logistic atBot (𝓝 0) := by
  have h1 : Tendsto (fun z : ℝ => Real.exp (-z)) atBot atTop :=
    Real.tendsto_exp_atTop.comp tendsto_neg_atBot_atTop
  have h2 : Tendsto (fun z : ℝ => 1 + Real.exp (-z)) atBot atTop :=
    tendsto_atTop_add_const_left atBot 1 h1
  refine h2.inv_tendsto_atTop.congr fun z => ?_
  simp [logistic]

/-! ## The standard normal density -/

/-- The standard normal density `φ(x) = e^{-x²/2} / √(2π)`. -/
def stdNormalPDF (x : ℝ) : ℝ := Real.exp (-(x ^ 2) / 2) / Real.sqrt (2 * Real.pi)

theorem sqrt_two_pi_pos : 0 < Real.sqrt (2 * Real.pi) :=
  Real.sqrt_pos.mpr (by positivity)

theorem stdNormalPDF_pos (x : ℝ) : 0 < stdNormalPDF x :=
  div_pos (Real.exp_pos _) sqrt_two_pi_pos

theorem stdNormalPDF_neg (x : ℝ) : stdNormalPDF (-x) = stdNormalPDF x := by
  simp [stdNormalPDF]

/-- `φ` is Mathlib's Gaussian density with mean `0` and variance `1`. -/
theorem stdNormalPDF_eq_gaussianPDFReal (x : ℝ) :
    stdNormalPDF x = gaussianPDFReal 0 1 x := by
  rw [stdNormalPDF, gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [div_eq_inv_mul]

/-- The density is largest at zero. -/
theorem stdNormalPDF_le_zero (x : ℝ) : stdNormalPDF x ≤ stdNormalPDF 0 := by
  unfold stdNormalPDF
  apply div_le_div_of_nonneg_right _ sqrt_two_pi_pos.le
  apply Real.exp_le_exp.mpr
  have := sq_nonneg x
  norm_num
  linarith

/-- The density is strictly largest at zero. -/
theorem stdNormalPDF_lt_zero {x : ℝ} (hx : x ≠ 0) : stdNormalPDF x < stdNormalPDF 0 := by
  unfold stdNormalPDF
  apply div_lt_div_of_pos_right _ sqrt_two_pi_pos
  apply Real.exp_lt_exp.mpr
  have : 0 < x ^ 2 := by positivity
  norm_num
  linarith

/-- The density vanishes in the right tail. -/
theorem tendsto_stdNormalPDF_atTop : Tendsto stdNormalPDF atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => -(x ^ 2) / 2) atTop atBot :=
    (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero)).atBot_div_const (by norm_num)
  have h2 := (Real.tendsto_exp_atBot.comp h1).div_const (Real.sqrt (2 * Real.pi))
  rw [zero_div] at h2
  exact h2

/-- The density vanishes in the left tail. -/
theorem tendsto_stdNormalPDF_atBot : Tendsto stdNormalPDF atBot (𝓝 0) := by
  have h := tendsto_stdNormalPDF_atTop.comp tendsto_neg_atBot_atTop
  have heq : stdNormalPDF ∘ (fun x => -x) = stdNormalPDF := by
    funext x
    simp [stdNormalPDF_neg]
  rwa [heq] at h

/-! ## The standard normal distribution function -/

/-- The standard normal distribution function `Φ`: the distribution function of Mathlib's
standard Gaussian measure `gaussianReal 0 1`. -/
def normalCDF (x : ℝ) : ℝ := cdf (gaussianReal 0 1) x

theorem continuous_gaussianPDFReal_zero_one : Continuous (gaussianPDFReal 0 1) := by
  rw [gaussianPDFReal_def]
  fun_prop

/-- `Φ(x) = ∫_{-∞}^{x} φ`. -/
theorem normalCDF_eq_integral (x : ℝ) :
    normalCDF x = ∫ y in Set.Iic x, gaussianPDFReal 0 1 y := by
  rw [normalCDF, cdf_eq_real, measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero,
    ENNReal.toReal_ofReal]
  exact setIntegral_nonneg measurableSet_Iic (fun y _ => gaussianPDFReal_nonneg 0 1 y)

/-- The derivative of the normal distribution function is the normal density: `Φ' = φ`. -/
theorem hasDerivAt_normalCDF (x : ℝ) : HasDerivAt normalCDF (stdNormalPDF x) x := by
  have hint : ∀ a : ℝ, IntegrableOn (gaussianPDFReal 0 1) (Set.Iic a) := fun a =>
    (integrable_gaussianPDFReal 0 1).integrableOn
  have heq : normalCDF = fun u => (∫ y in Set.Iic 0, gaussianPDFReal 0 1 y) +
      ∫ y in (0 : ℝ)..u, gaussianPDFReal 0 1 y := by
    funext u
    rw [normalCDF_eq_integral, ← intervalIntegral.integral_Iic_sub_Iic (hint 0) (hint u)]
    ring
  rw [heq, stdNormalPDF_eq_gaussianPDFReal]
  exact ((continuous_gaussianPDFReal_zero_one.integral_hasStrictDerivAt 0 x).hasDerivAt).const_add _

theorem normalCDF_continuous : Continuous normalCDF :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_normalCDF x).continuousAt

/-- `Φ` is strictly increasing. -/
theorem normalCDF_strictMono : StrictMono normalCDF :=
  strictMono_of_deriv_pos fun x => by
    rw [(hasDerivAt_normalCDF x).deriv]
    exact stdNormalPDF_pos x

theorem normalCDF_lt_one (x : ℝ) : normalCDF x < 1 :=
  lt_of_lt_of_le (normalCDF_strictMono (lt_add_one x)) (cdf_le_one (μ := gaussianReal 0 1) _)

theorem normalCDF_pos (x : ℝ) : 0 < normalCDF x :=
  lt_of_le_of_lt (cdf_nonneg (μ := gaussianReal 0 1) _) (normalCDF_strictMono (sub_one_lt x))

theorem tendsto_normalCDF_atBot : Tendsto normalCDF atBot (𝓝 0) :=
  tendsto_cdf_atBot (μ := gaussianReal 0 1)

theorem tendsto_normalCDF_atTop : Tendsto normalCDF atTop (𝓝 1) :=
  tendsto_cdf_atTop (μ := gaussianReal 0 1)

/-! ## A second-order remainder estimate -/

/-- If `f` has derivative `f'` near `x₀` and `f'` is differentiable at `x₀`, then the remainder of
the first-order expansion of `f` at `x₀` is `O((x - x₀)²)`. -/
theorem isBigO_sub_sub_deriv {f f' : ℝ → ℝ} {x₀ : ℝ}
    (hf : ∀ᶠ x in 𝓝 x₀, HasDerivAt f (f' x) x) (hf' : DifferentiableAt ℝ f' x₀) :
    (fun x => f x - f x₀ - f' x₀ * (x - x₀)) =O[𝓝 x₀] fun x => (x - x₀) ^ 2 := by
  obtain ⟨C, hCpos, hC⟩ := hf'.isBigO_sub.exists_pos
  have hCb := hC.bound
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hf.and hCb)
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [Metric.ball_mem_nhds x₀ hδ] with x hx
  have hxδ : |x - x₀| < δ := by
    rwa [Metric.mem_ball, Real.dist_eq] at hx
  have hsub : Metric.closedBall x₀ |x - x₀| ⊆ Metric.ball x₀ δ :=
    Metric.closedBall_subset_ball hxδ
  have hderiv : ∀ y ∈ Metric.closedBall x₀ |x - x₀|,
      HasDerivWithinAt (fun y => f y - f x₀ - f' x₀ * (y - x₀)) (f' y - f' x₀)
        (Metric.closedBall x₀ |x - x₀|) y := by
    intro y hy
    have hy' := (hball y (hsub hy)).1
    have h := (hy'.sub_const (f x₀)).sub (((hasDerivAt_id' y).sub_const x₀).const_mul (f' x₀))
    exact (h.congr_deriv (by ring)).hasDerivWithinAt
  have hbound : ∀ y ∈ Metric.closedBall x₀ |x - x₀|, ‖f' y - f' x₀‖ ≤ C * |x - x₀| := by
    intro y hy
    have h2 := (hball y (hsub hy)).2
    have hy' : |y - x₀| ≤ |x - x₀| := by
      rwa [Metric.mem_closedBall, Real.dist_eq] at hy
    calc ‖f' y - f' x₀‖ ≤ C * ‖y - x₀‖ := h2
      _ = C * |y - x₀| := by rw [Real.norm_eq_abs]
      _ ≤ C * |x - x₀| := mul_le_mul_of_nonneg_left hy' hCpos.le
  have hx0 : x₀ ∈ Metric.closedBall x₀ |x - x₀| := Metric.mem_closedBall_self (abs_nonneg _)
  have hx1 : x ∈ Metric.closedBall x₀ |x - x₀| := by
    rw [Metric.mem_closedBall, Real.dist_eq]
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_closedBall x₀ |x - x₀|) hx0 hx1
  simp only [sub_self, mul_zero, sub_zero] at key
  calc ‖f x - f x₀ - f' x₀ * (x - x₀)‖ ≤ C * |x - x₀| * ‖x - x₀‖ := key
    _ = C * ‖(x - x₀) ^ 2‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, sq]
      ring

end Chapeco
