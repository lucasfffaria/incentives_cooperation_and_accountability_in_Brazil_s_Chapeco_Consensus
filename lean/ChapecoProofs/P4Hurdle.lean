/-
Proposition 4 (completion hurdle), Supplementary Material 03, Section S3.4.

A conde who values the money at face value (`θ = 1`) chooses project `k`, considered on its own, if
and only if its net economies of scale exceed a hurdle, `σ > σ*(q)`, with

  `σ*(q) = f [v̄/(1 - d_c) - s_w(q)]/q_eff(q) - 1`,

where `q_eff(q) = q + (1 - q)(1 - ā) q β_d` and `s_w(q) = (1 - q)[(1 - ā)(1 - q) + ā] v_inc`.
The hurdle falls with expected completion unless the salvage value of unfinished works is large.

Variables: `vbar` is `v̄`, `dc` is `d_c`, `abar` is `ā`, `βd` is `β_d`, `vinc` is `v_inc`, `f` the
expected funded share, `C` the cost and `q` the completion probability.
-/
import ChapecoProofs.Basic

noncomputable section

open Real Filter Topology

namespace Chapeco.P4

/-- Probability of completion on time or, at a discount, a term late. -/
def qEff (abar βd q : ℝ) : ℝ := q + (1 - q) * (1 - abar) * q * βd

/-- Expected salvage value of unfinished works per real spent. -/
def sW (abar vinc q : ℝ) : ℝ := (1 - q) * ((1 - abar) * (1 - q) + abar) * vinc

/-- Expected value of an unfinished project. -/
def uUnf (abar βd vinc q V f C : ℝ) : ℝ :=
  (1 - abar) * (q * βd * V + (1 - q) * (vinc * f * C)) + abar * (vinc * f * C)

/-- The hurdle `σ*(q) = f [v̄/(1 - d_c) - s_w(q)]/q_eff(q) - 1`. -/
def hurdle (vbar dc abar βd vinc f q : ℝ) : ℝ :=
  f * (vbar / (1 - dc) - sW abar vinc q) / qEff abar βd q - 1

/-- **Step 2 (collecting terms).** With `V = (1 + σ) C`, the value of the project,
`(1 - d_c)[q V + (1 - q) U^unf]`, equals `(1 - d_c) C [(1 + σ) q_eff + f s_w]`. -/
theorem social_value_collect (dc abar βd vinc q σ f C : ℝ) :
    (1 - dc) * (q * ((1 + σ) * C) + (1 - q) * uUnf abar βd vinc q ((1 + σ) * C) f C) =
      (1 - dc) * C * ((1 + σ) * qEff abar βd q + f * sW abar vinc q) := by
  unfold uUnf qEff sW
  ring

/-- **Proposition 4 (Steps 1 to 3).** The inclusion rule `(1 - d_c)[q V + (1 - q) U^unf] > v̄ f C`
holds if and only if `σ > σ*(q)`. -/
theorem include_iff_hurdle {vbar dc abar βd vinc q σ f C : ℝ} (hC : 0 < C) (hdc : dc < 1)
    (hq : 0 < qEff abar βd q) :
    vbar * f * C < (1 - dc) * (q * ((1 + σ) * C) + (1 - q) * uUnf abar βd vinc q ((1 + σ) * C) f C)
      ↔ hurdle vbar dc abar βd vinc f q < σ := by
  rw [social_value_collect]
  have h1 : 0 < 1 - dc := by linarith
  have step1 : vbar * f * C < (1 - dc) * C * ((1 + σ) * qEff abar βd q + f * sW abar vinc q) ↔
      vbar * f < (1 - dc) * ((1 + σ) * qEff abar βd q + f * sW abar vinc q) := by
    rw [show (1 - dc) * C * ((1 + σ) * qEff abar βd q + f * sW abar vinc q) =
      (1 - dc) * ((1 + σ) * qEff abar βd q + f * sW abar vinc q) * C by ring]
    exact mul_lt_mul_right hC
  rw [step1, ← div_lt_iff₀' h1]
  unfold hurdle
  rw [sub_lt_iff_lt_add, div_lt_iff₀ hq,
    show f * (vbar / (1 - dc) - sW abar vinc q) = vbar * f / (1 - dc) - f * sW abar vinc q by ring,
    show σ + 1 = 1 + σ by ring]
  constructor <;> intro h <;> linarith

/-- `q_eff` is positive for `0 < q ≤ 1` and `(1 - ā) β_d ≥ 0`. -/
theorem qEff_pos {abar βd q : ℝ} (hk0 : 0 ≤ (1 - abar) * βd) (hq0 : 0 < q) (hq1 : q ≤ 1) :
    0 < qEff abar βd q := by
  unfold qEff
  have h := mul_nonneg (mul_nonneg (sub_nonneg.2 hq1) hk0) hq0.le
  nlinarith

/-- **Step 4.** `∂q_eff/∂q = 1 + (1 - ā) β_d (1 - 2q)`. -/
theorem hasDerivAt_qEff (abar βd q : ℝ) :
    HasDerivAt (fun q => qEff abar βd q) (1 + (1 - abar) * βd * (1 - 2 * q)) q := by
  have h := (hasDerivAt_id' q).add
    (((hasDerivAt_id' q).sub (hasDerivAt_pow 2 q)).const_mul ((1 - abar) * βd))
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  · norm_num
  · show qEff abar βd x = x + (1 - abar) * βd * (x - x ^ 2)
    unfold qEff
    ring

/-- **Step 4.** The effective completion increases with `q` for every `q ≤ 1`, in particular on
`[0, 1]`, because `0 ≤ (1 - ā) β_d < 1`. -/
theorem deriv_qEff_pos {abar βd q : ℝ} (hk0 : 0 ≤ (1 - abar) * βd) (hk1 : (1 - abar) * βd < 1)
    (hq1 : q ≤ 1) : 0 < 1 + (1 - abar) * βd * (1 - 2 * q) := by
  nlinarith [mul_nonneg hk0 (by linarith : (0 : ℝ) ≤ 2 - 2 * q)]

/-- **Step 4.** `∂s_w/∂q = -v_inc [2(1 - ā)(1 - q) + ā]`. -/
theorem hasDerivAt_sW (abar vinc q : ℝ) :
    HasDerivAt (fun q => sW abar vinc q) (-(vinc * (2 * (1 - abar) * (1 - q) + abar))) q := by
  have h := (((hasDerivAt_const q (1 : ℝ)).sub ((hasDerivAt_id' q).const_mul (2 - abar))).add
    ((hasDerivAt_pow 2 q).const_mul (1 - abar))).const_mul vinc
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  · norm_num
    ring
  · show sW abar vinc x = vinc * (1 - (2 - abar) * x + (1 - abar) * x ^ 2)
    unfold sW
    ring

/-- **Step 4.** The salvage term decreases with `q` on `[0, 1)` when `v_inc > 0` and `ā ∈ [0, 1]`.
(At `q = 1` the derivative is `-v_inc ā`, which is zero if `ā = 0`.) -/
theorem deriv_sW_neg {abar vinc q : ℝ} (hv : 0 < vinc) (ha0 : 0 ≤ abar) (ha1 : abar ≤ 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1) : -(vinc * (2 * (1 - abar) * (1 - q) + abar)) < 0 := by
  have h : 0 < 2 * (1 - abar) * (1 - q) + abar := by
    nlinarith [mul_pos (by linarith : (0 : ℝ) < 2 - abar) (by linarith : (0 : ℝ) < 1 - q),
      mul_nonneg ha0 hq0]
  have := mul_pos hv h
  linarith

/-- **Step 4.** The derivative of the hurdle with respect to `q`. -/
theorem hasDerivAt_hurdle {vbar dc abar βd vinc f q : ℝ} (hq : qEff abar βd q ≠ 0) :
    HasDerivAt (fun q => hurdle vbar dc abar βd vinc f q)
      (f * (vinc * (2 * (1 - abar) * (1 - q) + abar) * qEff abar βd q -
        (vbar / (1 - dc) - sW abar vinc q) * (1 + (1 - abar) * βd * (1 - 2 * q))) /
          qEff abar βd q ^ 2) q := by
  have hg : HasDerivAt (fun q => f * (vbar / (1 - dc) - sW abar vinc q))
      (f * (0 - -(vinc * (2 * (1 - abar) * (1 - q) + abar)))) q :=
    ((hasDerivAt_const q (vbar / (1 - dc))).sub (hasDerivAt_sW abar vinc q)).const_mul f
  have h := (hg.div (hasDerivAt_qEff abar βd q) hq).sub_const 1
  refine h.congr_deriv ?_
  ring

/-- **Step 4, condition (S3.4).** For `f > 0` and `q_eff > 0`, the hurdle falls with `q` if and only
if `v_inc [2(1 - ā)(1 - q) + ā] q_eff < [v̄/(1 - d_c) - s_w] ∂q_eff/∂q`. -/
theorem hurdle_deriv_neg_iff {vbar dc abar βd vinc f q : ℝ} (hf : 0 < f)
    (hq : 0 < qEff abar βd q) :
    f * (vinc * (2 * (1 - abar) * (1 - q) + abar) * qEff abar βd q -
        (vbar / (1 - dc) - sW abar vinc q) * (1 + (1 - abar) * βd * (1 - 2 * q))) /
          qEff abar βd q ^ 2 < 0 ↔
      vinc * (2 * (1 - abar) * (1 - q) + abar) * qEff abar βd q <
        (vbar / (1 - dc) - sW abar vinc q) * (1 + (1 - abar) * βd * (1 - 2 * q)) := by
  have h2 : 0 < qEff abar βd q ^ 2 := pow_pos hq 2
  rw [div_lt_iff₀ h2, zero_mul]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonneg hf.le (sub_nonneg.2 hc)]
  · intro h
    nlinarith [mul_pos hf (sub_pos.2 h)]

/-- **Step 4 (no salvage).** When unfinished works have no salvage value (`v_inc = 0`) and a real of
local money has positive value, the hurdle falls strictly with completion on `(0, 1]`. -/
theorem hurdle_strictAntiOn_no_salvage {vbar dc abar βd f : ℝ} (hf : 0 < f)
    (hB : 0 < vbar / (1 - dc)) (hk0 : 0 ≤ (1 - abar) * βd) (hk1 : (1 - abar) * βd < 1) :
    StrictAntiOn (fun q => hurdle vbar dc abar βd 0 f q) (Set.Ioc 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioc 0 1)
  · intro q hq
    exact (hasDerivAt_hurdle (vbar := vbar) (dc := dc) (vinc := 0) (f := f)
      (qEff_pos hk0 hq.1 hq.2).ne').continuousAt.continuousWithinAt
  · intro q hq
    rw [interior_Ioc] at hq
    have hqe := qEff_pos hk0 hq.1 hq.2.le
    rw [(hasDerivAt_hurdle (vbar := vbar) (dc := dc) (vinc := 0) (f := f) hqe.ne').deriv,
      hurdle_deriv_neg_iff hf hqe]
    have hd := deriv_qEff_pos hk0 hk1 hq.2.le
    have hs : sW abar 0 q = 0 := by
      unfold sW
      ring
    rw [hs, sub_zero, zero_mul, zero_mul]
    exact mul_pos hB hd

end Chapeco.P4
