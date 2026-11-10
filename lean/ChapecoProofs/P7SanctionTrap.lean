/-
Proposition 7 (the sanction trap), Supplementary Material 03, Section S3.7.

Completion `c` determines the probability of meeting the target, `Π(c)`, which determines the
continuity of the conde's office, which determines cooperation and next-term completion:

  `c' = Γ(c) = Q Λ((g₀ + β π_w [κ_P + (1 - κ_P) Π(c)] F)/ς)`.

(i) Without the bar, `Γ` does not depend on `c` and the steady state is unique. (ii) With the bar
and `κ_P < 1`, `Γ` lies below its no-bar value for every `c`. (iii) When `Γ` crosses the diagonal
from below (`Γ' > 1` at the crossing), there are steady states on both sides of the crossing, so a
county can be held at low completion; peer comparison moves the threshold toward each county's own
capacity.

What is formalized here: (i), (ii), the properties of `Γ` used in Step 3 (positive at `0`, below
`1` at `1`, increasing, continuous), the existence of a steady state, the existence of a steady
state on each side of a crossing from below (`three_steady_states`), and the monotonicity of `Γ`
in capacity (Step 4). Not formalized: the local stability of the steady states (`Γ' < 1` at a
crossing) and the numerical example.

In this file `Pass` stands for `Π`, `cap` for the capacity `μ`, `πw` for `π_w` and `κ` for `κ_P`.
-/
import ChapecoProofs.Basic

noncomputable section

open Real Filter Topology

namespace Chapeco.P7

/-- The completion map `Γ(c) = Q Λ((g₀ + β π_w [κ + (1 - κ) Π(c)] F)/ς)`. -/
def completionMap (Q g0 β πw κ F ς : ℝ) (Pass : ℝ → ℝ) (c : ℝ) : ℝ :=
  Q * logistic ((g0 + β * πw * (κ + (1 - κ) * Pass c) * F) / ς)

/-- The value of the map without the bar, where the bracket is one. -/
def noBarValue (Q g0 β πw F ς : ℝ) : ℝ := Q * logistic ((g0 + β * πw * F) / ς)

/-- The probability of meeting the target, `Π(c) = Φ((μ + b c - z̄)/σ)`. -/
def passProb (cap b zbar σ c : ℝ) : ℝ := normalCDF ((cap + b * c - zbar) / σ)

/-! ## (i) No bar -/

/-- **(i), Step 1.** Without the bar the bracket is one, so `Γ` is constant. -/
theorem no_bar_constant (Q g0 β πw κ F ς c : ℝ) :
    completionMap Q g0 β πw κ F ς (fun _ => 1) c = noBarValue Q g0 β πw F ς := by
  unfold completionMap noBarValue
  have h : κ + (1 - κ) = 1 := by ring
  simp only [mul_one, h]

/-- **(i), Step 1.** Hence the steady state without the bar is unique. -/
theorem no_bar_unique_steady_state (Q g0 β πw κ F ς c : ℝ) :
    completionMap Q g0 β πw κ F ς (fun _ => 1) c = c ↔ c = noBarValue Q g0 β πw F ς := by
  rw [no_bar_constant]
  exact eq_comm

/-! ## (ii) The bar lowers the map -/

/-- **(ii), Step 2.** With the bar and `κ_P < 1`, `Γ(c)` is below its no-bar value whenever
`Π(c) < 1`. -/
theorem bar_lowers_map {Q g0 β πw κ F ς : ℝ} {Pass : ℝ → ℝ} (hQ : 0 < Q) (hς : 0 < ς)
    (hpos : 0 < β * πw * F) (hκ : κ < 1) {c : ℝ} (hP : Pass c < 1) :
    completionMap Q g0 β πw κ F ς Pass c < noBarValue Q g0 β πw F ς := by
  unfold completionMap noBarValue
  apply mul_lt_mul_of_pos_left _ hQ
  apply logistic_strictMono
  apply div_lt_div_of_pos_right _ hς
  have hb : κ + (1 - κ) * Pass c < 1 := by
    nlinarith [mul_pos (sub_pos.2 hκ) (sub_pos.2 hP)]
  nlinarith [mul_lt_mul_of_pos_left hb hpos]

/-- **(ii), Step 2.** With the normal distribution function, `Π(c) < 1` for every `c`, so the bar
lowers `Γ` everywhere. -/
theorem bar_lowers_map_normal {Q g0 β πw κ F ς cap b zbar σ : ℝ} (hQ : 0 < Q) (hς : 0 < ς)
    (hpos : 0 < β * πw * F) (hκ : κ < 1) (c : ℝ) :
    completionMap Q g0 β πw κ F ς (passProb cap b zbar σ) c < noBarValue Q g0 β πw F ς :=
  bar_lowers_map hQ hς hpos hκ (normalCDF_lt_one _)

/-! ## (iii) Steady states -/

theorem completionMap_pos {Q g0 β πw κ F ς : ℝ} {Pass : ℝ → ℝ} (hQ : 0 < Q) (c : ℝ) :
    0 < completionMap Q g0 β πw κ F ς Pass c :=
  mul_pos hQ (logistic_pos _)

theorem completionMap_lt_one {Q g0 β πw κ F ς : ℝ} {Pass : ℝ → ℝ} (hQ0 : 0 < Q) (hQ1 : Q ≤ 1)
    (c : ℝ) : completionMap Q g0 β πw κ F ς Pass c < 1 := by
  unfold completionMap
  have := logistic_lt_one ((g0 + β * πw * (κ + (1 - κ) * Pass c) * F) / ς)
  nlinarith [logistic_pos ((g0 + β * πw * (κ + (1 - κ) * Pass c) * F) / ς)]

/-- `Γ` is monotone in the value of `Π`. -/
theorem completionMap_le_of_le {Q g0 β πw κ F ς : ℝ} {P₁ P₂ : ℝ → ℝ} {c₁ c₂ : ℝ} (hQ : 0 ≤ Q)
    (hς : 0 < ς) (hpos : 0 ≤ β * πw * F) (hκ : κ ≤ 1) (h : P₁ c₁ ≤ P₂ c₂) :
    completionMap Q g0 β πw κ F ς P₁ c₁ ≤ completionMap Q g0 β πw κ F ς P₂ c₂ := by
  unfold completionMap
  apply mul_le_mul_of_nonneg_left _ hQ
  apply logistic_strictMono.monotone
  apply div_le_div_of_nonneg_right _ hς.le
  nlinarith [mul_nonneg hpos (mul_nonneg (sub_nonneg.2 hκ) (sub_nonneg.2 h))]

/-- **Step 3.** `Γ` is increasing when `Π` is. -/
theorem completionMap_monotone {Q g0 β πw κ F ς : ℝ} {Pass : ℝ → ℝ} (hQ : 0 ≤ Q) (hς : 0 < ς)
    (hpos : 0 ≤ β * πw * F) (hκ : κ ≤ 1) (hP : Monotone Pass) :
    Monotone (completionMap Q g0 β πw κ F ς Pass) :=
  fun _ _ hab => completionMap_le_of_le hQ hς hpos hκ (hP hab)

/-- **Step 3.** `Γ` is continuous when `Π` is. -/
theorem completionMap_continuous {Q g0 β πw κ F ς : ℝ} {Pass : ℝ → ℝ} (hP : Continuous Pass) :
    Continuous (completionMap Q g0 β πw κ F ς Pass) := by
  have hl := logistic_continuous
  show Continuous fun c => Q * logistic ((g0 + β * πw * (κ + (1 - κ) * Pass c) * F) / ς)
  fun_prop

theorem passProb_continuous (cap b zbar σ : ℝ) : Continuous (passProb cap b zbar σ) := by
  have hn := normalCDF_continuous
  show Continuous fun c => normalCDF ((cap + b * c - zbar) / σ)
  fun_prop

theorem passProb_monotone {cap b zbar σ : ℝ} (hb : 0 ≤ b) (hσ : 0 < σ) :
    Monotone (passProb cap b zbar σ) := by
  intro x y hxy
  unfold passProb
  apply normalCDF_strictMono.monotone
  apply div_le_div_of_nonneg_right _ hσ.le
  nlinarith [mul_le_mul_of_nonneg_left hxy hb]

/-- **Step 3.** A continuous map with `Γ(0) > 0` and `Γ(1) < 1` has a steady state in `(0, 1)`. -/
theorem exists_steady_state {Γ : ℝ → ℝ} (hΓ : ContinuousOn Γ (Set.Icc 0 1)) (h0 : 0 < Γ 0)
    (h1 : Γ 1 < 1) : ∃ c ∈ Set.Ioo (0 : ℝ) 1, Γ c = c := by
  have hf : ContinuousOn (fun c => Γ c - c) (Set.Icc 0 1) := hΓ.sub continuousOn_id
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Ioo' zero_le_one hf
    (show (0 : ℝ) ∈ Set.Ioo (Γ 1 - 1) (Γ 0 - 0) from ⟨by linarith, by linarith⟩)
  refine ⟨c, hc, ?_⟩
  have : Γ c - c = 0 := hfc
  linarith

/-- **Step 3 (three steady states).** If `Γ` is continuous on `[0, 1]`, with `Γ(0) > 0` and
`Γ(1) < 1`, and crosses the diagonal from below at `ch ∈ (0, 1)` (the point `ĉ` of the
supplement: `Γ(ch) = ch` and `Γ'(ch) > 1`), then there is a steady state on each side of `ch`. -/
theorem three_steady_states {Γ : ℝ → ℝ} (hΓ : ContinuousOn Γ (Set.Icc 0 1)) (h0 : 0 < Γ 0)
    (h1 : Γ 1 < 1) {ch d : ℝ} (hch0 : 0 < ch) (hch1 : ch < 1) (hfix : Γ ch = ch)
    (hd : HasDerivAt Γ d ch) (hd1 : 1 < d) :
    (∃ c₁ ∈ Set.Ioo 0 ch, Γ c₁ = c₁) ∧ (∃ c₂ ∈ Set.Ioo ch 1, Γ c₂ = c₂) := by
  have hfd : HasDerivAt (fun c => Γ c - c) (d - 1) ch := hd.sub (hasDerivAt_id' ch)
  have hfch : Γ ch - ch = 0 := sub_eq_zero.2 hfix
  have hslope : ∀ᶠ c in 𝓝[≠] ch, 0 < slope (fun c => Γ c - c) ch c :=
    (hasDerivAt_iff_tendsto_slope.1 hfd).eventually (lt_mem_nhds (by linarith : (0 : ℝ) < d - 1))
  have hcont : ContinuousOn (fun c => Γ c - c) (Set.Icc 0 1) := hΓ.sub continuousOn_id
  constructor
  · have hleft : ∀ᶠ c in 𝓝[<] ch, 0 < slope (fun c => Γ c - c) ch c ∧ c ∈ Set.Ioo 0 ch :=
      (hslope.filter_mono (nhdsWithin_mono ch fun x hx => (show x < ch from hx).ne)).and
        (Ioo_mem_nhdsLT hch0)
    obtain ⟨c₀, hs, hc₀⟩ := hleft.exists
    have hneg : c₀ - ch < 0 := by linarith [hc₀.2]
    rw [slope_def_field, hfch, sub_zero] at hs
    have hfc₀ : Γ c₀ - c₀ < 0 :=
      (div_pos_iff.1 hs).elim (fun h => absurd h.2 (not_lt.2 hneg.le)) (fun h => h.1)
    have hsub : Set.Icc 0 c₀ ⊆ Set.Icc 0 1 := Set.Icc_subset_Icc le_rfl (by linarith [hc₀.2])
    obtain ⟨c, hc, hfc⟩ := intermediate_value_Ioo' hc₀.1.le (hcont.mono hsub)
      (show (0 : ℝ) ∈ Set.Ioo (Γ c₀ - c₀) (Γ 0 - 0) from ⟨hfc₀, by linarith⟩)
    refine ⟨c, ⟨hc.1, by linarith [hc.2, hc₀.2]⟩, ?_⟩
    have : Γ c - c = 0 := hfc
    linarith
  · have hright : ∀ᶠ c in 𝓝[>] ch, 0 < slope (fun c => Γ c - c) ch c ∧ c ∈ Set.Ioo ch 1 :=
      (hslope.filter_mono (nhdsWithin_mono ch fun x hx => (show ch < x from hx).ne')).and
        (Ioo_mem_nhdsGT hch1)
    obtain ⟨c₀, hs, hc₀⟩ := hright.exists
    have hpos : 0 < c₀ - ch := by linarith [hc₀.1]
    rw [slope_def_field, hfch, sub_zero] at hs
    have hfc₀ : 0 < Γ c₀ - c₀ :=
      (div_pos_iff.1 hs).elim (fun h => h.1) (fun h => absurd h.2 (not_lt.2 hpos.le))
    have hsub : Set.Icc c₀ 1 ⊆ Set.Icc 0 1 := Set.Icc_subset_Icc (by linarith [hc₀.1]) le_rfl
    obtain ⟨c, hc, hfc⟩ := intermediate_value_Ioo' hc₀.2.le (hcont.mono hsub)
      (show (0 : ℝ) ∈ Set.Ioo (Γ 1 - 1) (Γ c₀ - c₀) from ⟨by linarith, hfc₀⟩)
    refine ⟨c, ⟨by linarith [hc.1, hc₀.1], hc.2⟩, ?_⟩
    have : Γ c - c = 0 := hfc
    linarith

/-- **Proposition 7 (iii).** For the completion map with the normal `Π` and `0 < Q ≤ 1`, a crossing
of the diagonal from below at `ch ∈ (0, 1)` implies a steady state on each side of `ch`. -/
theorem sanction_trap {Q g0 β πw κ F ς cap b zbar σ : ℝ} (hQ0 : 0 < Q) (hQ1 : Q ≤ 1) {ch d : ℝ}
    (hch0 : 0 < ch) (hch1 : ch < 1)
    (hfix : completionMap Q g0 β πw κ F ς (passProb cap b zbar σ) ch = ch)
    (hd : HasDerivAt (completionMap Q g0 β πw κ F ς (passProb cap b zbar σ)) d ch) (hd1 : 1 < d) :
    (∃ c₁ ∈ Set.Ioo 0 ch, completionMap Q g0 β πw κ F ς (passProb cap b zbar σ) c₁ = c₁) ∧
      (∃ c₂ ∈ Set.Ioo ch 1, completionMap Q g0 β πw κ F ς (passProb cap b zbar σ) c₂ = c₂) :=
  three_steady_states (completionMap_continuous (passProb_continuous cap b zbar σ)).continuousOn
    (completionMap_pos hQ0 0) (completionMap_lt_one hQ0 hQ1 1) hch0 hch1 hfix hd hd1

/-! ## Step 4: capacity and peer comparison -/

/-- **Step 4.** `Γ(c)` increases with the county's capacity relative to the threshold, so a rule
that raises `μ - z̄` for low-capacity counties (peer comparison) raises their completion map. -/
theorem completionMap_mono_capacity {Q g0 β πw κ F ς b zbar σ c : ℝ} (hQ : 0 ≤ Q) (hς : 0 < ς)
    (hpos : 0 ≤ β * πw * F) (hκ : κ ≤ 1) (hσ : 0 < σ) :
    Monotone fun cap => completionMap Q g0 β πw κ F ς (passProb cap b zbar σ) c := by
  intro x y hxy
  apply completionMap_le_of_le hQ hς hpos hκ
  unfold passProb
  apply normalCDF_strictMono.monotone
  apply div_le_div_of_nonneg_right _ hσ.le
  linarith

/-- **Step 4.** In low-capacity counties `Π(c)` is close to zero. -/
theorem passProb_tendsto_zero {b zbar σ : ℝ} (hσ : 0 < σ) (c : ℝ) :
    Tendsto (fun cap => passProb cap b zbar σ c) atBot (𝓝 0) := by
  have h : Tendsto (fun cap : ℝ => (cap + b * c - zbar) / σ) atBot atBot :=
    tendsto_atBot_atBot.2 fun B => ⟨B * σ - b * c + zbar, fun x hx => by
      show (x + b * c - zbar) / σ ≤ B
      rw [div_le_iff₀ hσ]
      linarith⟩
  exact tendsto_normalCDF_atBot.comp h

end Chapeco.P7
