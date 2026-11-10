/-
Proposition 2 (effort and relocation), Supplementary Material 03, Section S3.2.

After the reform, a deputy of party `p` devotes a share `e_B = X s₀/(X s₀ + 1 - s₀)` of effort to
brokerage, where `X = π ψ/κ` and `ψ = η + χ (1 - η) s̄` is the brokerage technology that survives
the abolition of amendments. Legislative effort rises if and only if `X < 1`. If `η = 1`, abolition
adds nothing to closed lists; otherwise, and if `χ > 0`, parties whose condes control more county
money keep more brokerage.

In this file the multiplier `π` of the text is written `piB`, because `π` is reserved for the
number pi.
-/
import ChapecoProofs.Basic

noncomputable section

open Real

namespace Chapeco.P2

/-- The deputy's objective, `W_B ln e + W_L ln(1 - e)`. -/
def careerValue (WB WL e : ℝ) : ℝ := WB * Real.log e + WL * Real.log (1 - e)

/-- The share of effort devoted to brokerage, as a function of the status-quo share `s₀` and of the
ratio `X` of the multipliers of the two weights. -/
def brokerShare (s₀ X : ℝ) : ℝ := X * s₀ / (X * s₀ + 1 - s₀)

/-- The brokerage technology that survives the abolition of amendments. -/
def psi (η χ sbar : ℝ) : ℝ := η + χ * (1 - η) * sbar

theorem one_sub_share {WB WL : ℝ} (hS : 0 < WB + WL) :
    1 - WB / (WB + WL) = WL / (WB + WL) := by
  field_simp

/-- **Step 1.** The share `W_B/(W_B + W_L)` maximizes the objective on `(0,1)`. -/
theorem careerValue_le {WB WL : ℝ} (hB : 0 < WB) (hL : 0 < WL) {e : ℝ} (he0 : 0 < e)
    (he1 : e < 1) : careerValue WB WL e ≤ careerValue WB WL (WB / (WB + WL)) := by
  have hS : 0 < WB + WL := by linarith
  have hs0 : 0 < WB / (WB + WL) := div_pos hB hS
  have hs1 : 0 < 1 - WB / (WB + WL) := by
    rw [one_sub_share hS]
    exact div_pos hL hS
  have h1 : Real.log e - Real.log (WB / (WB + WL)) ≤ e / (WB / (WB + WL)) - 1 := by
    rw [← Real.log_div he0.ne' hs0.ne']
    exact Real.log_le_sub_one_of_pos (div_pos he0 hs0)
  have h2 : Real.log (1 - e) - Real.log (1 - WB / (WB + WL)) ≤
      (1 - e) / (1 - WB / (WB + WL)) - 1 := by
    rw [← Real.log_div (sub_pos.2 he1).ne' hs1.ne']
    exact Real.log_le_sub_one_of_pos (div_pos (by linarith) hs1)
  have h3 : WB * (e / (WB / (WB + WL)) - 1) + WL * ((1 - e) / (1 - WB / (WB + WL)) - 1) = 0 := by
    rw [one_sub_share hS]
    field_simp
    ring
  unfold careerValue
  nlinarith [mul_le_mul_of_nonneg_left h1 hB.le, mul_le_mul_of_nonneg_left h2 hL.le]

/-- **Step 1 (uniqueness).** Any other share gives a strictly lower value. -/
theorem careerValue_lt {WB WL : ℝ} (hB : 0 < WB) (hL : 0 < WL) {e : ℝ} (he0 : 0 < e)
    (he1 : e < 1) (hne : e ≠ WB / (WB + WL)) :
    careerValue WB WL e < careerValue WB WL (WB / (WB + WL)) := by
  have hS : 0 < WB + WL := by linarith
  have hs0 : 0 < WB / (WB + WL) := div_pos hB hS
  have hs1 : 0 < 1 - WB / (WB + WL) := by
    rw [one_sub_share hS]
    exact div_pos hL hS
  have hratio : e / (WB / (WB + WL)) ≠ 1 := by
    intro h
    exact hne ((div_eq_one_iff_eq hs0.ne').1 h)
  have h1 : Real.log e - Real.log (WB / (WB + WL)) < e / (WB / (WB + WL)) - 1 := by
    rw [← Real.log_div he0.ne' hs0.ne']
    exact Real.log_lt_sub_one_of_pos (div_pos he0 hs0) hratio
  have h2 : Real.log (1 - e) - Real.log (1 - WB / (WB + WL)) ≤
      (1 - e) / (1 - WB / (WB + WL)) - 1 := by
    rw [← Real.log_div (sub_pos.2 he1).ne' hs1.ne']
    exact Real.log_le_sub_one_of_pos (div_pos (by linarith) hs1)
  have h3 : WB * (e / (WB / (WB + WL)) - 1) + WL * ((1 - e) / (1 - WB / (WB + WL)) - 1) = 0 := by
    rw [one_sub_share hS]
    field_simp
    ring
  unfold careerValue
  nlinarith [mul_lt_mul_of_pos_left h1 hB, mul_le_mul_of_nonneg_left h2 hL.le]

/-- **Step 1 (status quo).** The status-quo share `s₀` pins down the ratio of the weights:
`W_L = W_B (1 - s₀)/s₀`. -/
theorem weight_ratio {WB WL : ℝ} (hB : 0 < WB) (hL : 0 < WL) :
    WL = WB * (1 - WB / (WB + WL)) / (WB / (WB + WL)) := by
  have hS : 0 < WB + WL := by linarith
  rw [one_sub_share hS]
  field_simp

/-- **Step 2.** After the reform the weights are `π ψ W_B` and `κ W_L`, and the brokerage share is
`X s₀/(X s₀ + 1 - s₀)` with `X = π ψ/κ` and `s₀ = W_B/(W_B + W_L)`. -/
theorem effort_after_reform {WB WL P κ : ℝ} (hB : 0 < WB) (hL : 0 < WL) (hP : 0 < P)
    (hκ : 0 < κ) :
    P * WB / (P * WB + κ * WL) = brokerShare (WB / (WB + WL)) (P / κ) := by
  have hS : 0 < WB + WL := by linarith
  have hS' : WB + WL ≠ 0 := hS.ne'
  have hκ' : κ ≠ 0 := hκ.ne'
  have hden : P * WB + κ * WL ≠ 0 := by positivity
  unfold brokerShare
  rw [add_sub_assoc, one_sub_share hS]
  field_simp
  ring

/-- **Proposition 2 (effort).** The post-reform objective `(π ψ W_B) ln e + (κ W_L) ln(1 - e)` is
maximized at the share `brokerShare s₀ (π ψ/κ)`. -/
theorem proposition2_effort {WB WL piB ψ κ : ℝ} (hB : 0 < WB) (hL : 0 < WL) (hP : 0 < piB * ψ)
    (hκ : 0 < κ) {e : ℝ} (he0 : 0 < e) (he1 : e < 1) :
    careerValue (piB * ψ * WB) (κ * WL) e ≤
      careerValue (piB * ψ * WB) (κ * WL) (brokerShare (WB / (WB + WL)) (piB * ψ / κ)) := by
  rw [← effort_after_reform hB hL hP hκ]
  exact careerValue_le (mul_pos hP hB) (mul_pos hκ hL) he0 he1

theorem brokerShare_one (s₀ : ℝ) : brokerShare s₀ 1 = s₀ := by
  unfold brokerShare
  simp

theorem brokerShare_den_pos {s₀ X : ℝ} (h0 : 0 < s₀) (h1 : s₀ < 1) (hX : 0 ≤ X) :
    0 < X * s₀ + 1 - s₀ := by
  nlinarith [mul_nonneg hX h0.le]

/-- **Step 3.** The brokerage share is strictly increasing in `X`. -/
theorem brokerShare_strictMonoOn {s₀ : ℝ} (h0 : 0 < s₀) (h1 : s₀ < 1) :
    StrictMonoOn (brokerShare s₀) (Set.Ici 0) := by
  intro X hX Y hY hXY
  simp only [Set.mem_Ici] at hX hY
  unfold brokerShare
  rw [div_lt_div_iff₀ (brokerShare_den_pos h0 h1 hX) (brokerShare_den_pos h0 h1 hY)]
  nlinarith [mul_pos (sub_pos.2 hXY) (mul_pos h0 (sub_pos.2 h1))]

/-- **Step 3.** Legislative effort `1 - e_B` rises above its status-quo value `1 - s₀` if and only
if `X < 1`. -/
theorem legislative_effort_rises_iff {s₀ X : ℝ} (h0 : 0 < s₀) (h1 : s₀ < 1) (hX : 0 ≤ X) :
    1 - s₀ < 1 - brokerShare s₀ X ↔ X < 1 := by
  rw [sub_lt_sub_iff_left]
  have h := (brokerShare_strictMonoOn h0 h1).lt_iff_lt (a := X) (b := 1) hX
    (Set.mem_Ici.2 zero_le_one)
  rwa [brokerShare_one] at h

/-- **Step 4.** If the whole abolished amount reappears in discretionary channels (`η = 1`), the
surviving technology is one for every party, and `X = π/κ`, its value under closed lists without
abolition. -/
theorem psi_of_eta_one (χ sbar : ℝ) : psi 1 χ sbar = 1 := by
  unfold psi
  ring

/-- **Step 4.** For `η < 1` and `χ > 0`, the surviving technology increases with the share of
county money controlled by the party's condes. -/
theorem psi_strictMono {η χ : ℝ} (hη : η < 1) (hχ : 0 < χ) : StrictMono (psi η χ) := by
  intro a b hab
  unfold psi
  have : 0 < χ * (1 - η) := mul_pos hχ (by linarith)
  nlinarith

/-- **Step 4.** Hence, for `0 ≤ η < 1` and `χ > 0`, parties whose condes control more county money
keep more brokerage. -/
theorem brokerage_increasing_in_county_money {η χ piB κ s₀ : ℝ} (hη0 : 0 ≤ η) (hη : η < 1)
    (hχ : 0 < χ) (hπ : 0 < piB) (hκ : 0 < κ) (h0 : 0 < s₀) (h1 : s₀ < 1) :
    StrictMonoOn (fun sbar => brokerShare s₀ (piB * psi η χ sbar / κ)) (Set.Ici 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  have hpsi : ∀ x : ℝ, 0 ≤ x → 0 ≤ psi η χ x := by
    intro x hx
    unfold psi
    have : 0 ≤ χ * (1 - η) * x := mul_nonneg (mul_nonneg hχ.le (by linarith)) hx
    linarith
  apply brokerShare_strictMonoOn h0 h1
  · exact div_nonneg (mul_nonneg hπ.le (hpsi a ha)) hκ.le
  · exact div_nonneg (mul_nonneg hπ.le (hpsi b hb)) hκ.le
  · exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left (psi_strictMono hη hχ hab) hπ) hκ

end Chapeco.P2
