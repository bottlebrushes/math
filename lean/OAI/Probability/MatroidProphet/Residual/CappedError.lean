import OAI.Probability.MatroidProphet.Residual.CappedTail
import OAI.Probability.MatroidProphet.Residual.Constants
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Expected transfer error with a capped generator budget

For a group of `N ≥ κ` labels (`κ = ruleKappa`), the capped budget `capBudget N = ⌊N/2⌋ / κ`
admits a residual family of size `exp(Λ N)` with `Λ = residualExponent (2κ)`. The transfer gap is
at most the largest captured residual plus `N` on the event that the density sample has more
than `N/2` labels. The first term has expectation `Λ N / log(1/p_O) + 1/(1-p_O)` (layer cake at
the mask-union rate `p_O`); the second is a Chernoff tail at density rate `7/16`.
-/

namespace OAI

namespace MatroidProphet
open Finset Pivots
variable {α : Type*} [DecidableEq α]

set_option linter.unusedSectionVars false

/-- Real budget denominator: `capBudget N ≤ N / cappedThreshold`. -/
noncomputable def cappedThreshold : ℝ := 2 * ruleKappa

lemma capBudget_le (N : ℕ) : (capBudget N : ℝ) ≤ (N : ℝ) / cappedThreshold := by
  unfold capBudget cappedThreshold
  have h1 : ((N / 2 / ruleKappa : ℕ) : ℝ) * ruleKappa ≤ (N / 2 : ℕ) := by
    exact_mod_cast Nat.div_mul_le_self _ _
  have h2 : ((N / 2 : ℕ) : ℝ) * 2 ≤ (N : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self _ _
  have hk : (0 : ℝ) < ruleKappa := by exact_mod_cast ruleKappa_pos
  rw [le_div_iff₀ (by positivity)]
  nlinarith

lemma two_le_cappedThreshold : (2 : ℝ) ≤ cappedThreshold := by
  norm_num [cappedThreshold, ruleKappa]

lemma capped_exponent_le :
    residualExponent cappedThreshold ≤ (5 + 2539 / 41 * Real.log 2) / 3072 := by
  have hl := Real.log_two_gt_d9
  have h3 := log_three_le
  have hkv : cappedThreshold = 3 * 2 ^ 10 := by norm_num [cappedThreshold, ruleKappa]
  have hL1 : Real.log cappedThreshold = Real.log 3 + 10 * Real.log 2 := by
    rw [hkv, Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
  have hL2 : Real.log (cappedThreshold / 2) = Real.log 3 + 9 * Real.log 2 := by
    rw [hkv, show (3 * 2 ^ 10 / 2 : ℝ) = 3 * 2 ^ 9 by norm_num,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
  have hL4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  unfold residualExponent
  rw [hL1, hL2, hL4, hkv, show (3 * 2 ^ 10 : ℝ) = 3072 by norm_num]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  linarith

lemma residualExponent_nonneg_capped : 0 ≤ residualExponent cappedThreshold := by
  unfold residualExponent cappedThreshold
  have hk : (2 : ℝ) ≤ 2 * ruleKappa := by
    have : (1 : ℝ) ≤ ruleKappa := by exact_mod_cast ruleKappa_pos
    linarith
  have h1 : 0 ≤ Real.log (2 * (ruleKappa : ℝ)) := Real.log_nonneg (by linarith)
  have h2 : 0 ≤ Real.log (2 * (ruleKappa : ℝ) / 2) := Real.log_nonneg (by
    rw [le_div_iff₀ (by norm_num)]; linarith)
  have h3 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  positivity

/-- `log (1/p_O) ≥ (149/125) log 2`. -/
lemma log_inv_maskUnionRate_ge : 149 / 125 * Real.log 2 ≤ Real.log (1 / maskUnionRate) := by
  have hρ : maskUnionRate ≤ 547 / 1250 := by norm_num [maskUnionRate, densityRate, thinningRate]
  have hρ0 := maskUnionRate_pos
  have hpow : Real.log ((2 : ℝ) ^ 149) ≤ Real.log ((1250 / 547 : ℝ) ^ 125) :=
    Real.log_le_log (by positivity) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at hpow
  have hmono : Real.log (1250 / 547 : ℝ) ≤ Real.log (1 / maskUnionRate) :=
    Real.log_le_log (by norm_num) (by rw [div_le_div_iff₀ (by norm_num) hρ0]; linarith)
  push_cast at hpow
  linarith

/-- Chernoff bound for the density sample above `N/2`. -/
noncomputable def densityCapTail : ℝ := (3 / 8) ^ 12

lemma capped_residual_numeric :
    residualExponent cappedThreshold / Real.log (1 / maskUnionRate) +
        1 / (1 - maskUnionRate) / ruleKappa + densityCapTail ≤ residualError := by
  have hΛ := capped_exponent_le
  have hl := Real.log_two_gt_d9
  have hl' := Real.log_two_lt_d9
  have hlog := log_inv_maskUnionRate_ge
  have hden : 0 < 149 / 125 * Real.log 2 := by positivity
  have hΛ0 := residualExponent_nonneg_capped
  have h1 : residualExponent cappedThreshold / Real.log (1 / maskUnionRate) ≤
      (5 + 2539 / 41 * Real.log 2) / 3072 / (149 / 125 * Real.log 2) :=
    div_le_div₀ (by positivity) hΛ hden hlog
  have h2 : (5 + 2539 / 41 * Real.log 2) / 3072 / (149 / 125 * Real.log 2) ≤
      residualError - 1 / (1 - maskUnionRate) / ruleKappa - densityCapTail := by
    rw [div_le_iff₀ hden]
    norm_num [maskUnionRate, densityRate, thinningRate, ruleKappa, residualError, densityCapTail]
    nlinarith
  linarith

/-- The Chernoff tail of a density sample above `N/2`. -/
theorem density_cap_tail_le (V : Finset α) (hN : ruleKappa ≤ V.card) :
    bitsExpectation (fun _ => densityRate) V
        (fun A => if capBudget V.card < A.card / ruleKappa then (1 : ℝ) else 0) ≤
      densityCapTail := by
  set N := V.card
  set m := N / 2
  set s : ℝ := 9 / 8
  have hp0 : (0 : ℝ) ≤ densityRate := by norm_num [densityRate]
  have hp1 : densityRate ≤ (1 : ℝ) := by norm_num [densityRate]
  have hr : (1 : ℝ) ≤ s ^ 2 := one_le_pow₀ (by norm_num [s])
  have hind (A : Finset α) : (if capBudget N < A.card / ruleKappa then (1 : ℝ) else 0) ≤
      (if m < A.card then (1 : ℝ) else 0) := by
    by_cases h : capBudget N < A.card / ruleKappa
    · have hm : m < A.card := by
        by_contra hle
        push Not at hle
        exact absurd h (not_lt.mpr (Nat.div_le_div_right (c := ruleKappa) hle))
      simp only [h, hm, ite_true, le_refl]
    · simp only [h, ite_false]; split_ifs <;> norm_num
  have hchern := bitsExpectation_card_gt_le densityRate (s ^ 2) hp0 hp1 hr V m
  have hc : (1 - densityRate + densityRate * s ^ 2) ≤ (127 / 128) * s := by
    norm_num [densityRate, s]
  have hexp : N ≤ 2 * (m + 1) := by omega
  have hpow : s ^ N ≤ (s ^ 2) ^ (m + 1) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num [s]) hexp
  have hspos : 0 < s := by norm_num [s]
  have hbase0 : 0 ≤ 1 - densityRate + densityRate * s ^ 2 := by
    have := pow_nonneg hspos.le 2
    nlinarith
  have hgeo : (127 / 128 : ℝ) ^ N ≤ densityCapTail := by
    have hk : 1536 ≤ N := by simpa [ruleKappa] using hN
    calc (127 / 128 : ℝ) ^ N ≤ (127 / 128) ^ 1536 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
      _ = ((127 / 128 : ℝ) ^ 128) ^ 12 := by rw [← pow_mul]
      _ ≤ (3 / 8) ^ 12 := pow_le_pow_left₀ (by positivity) (by norm_num) 12
      _ = densityCapTail := rfl
  calc _ ≤ bitsExpectation (fun _ => densityRate) V (fun A => if m < A.card then (1 : ℝ) else 0) :=
        bitsExpectation_mono _ (fun _ => hp0) (fun _ => hp1) V (fun A _ => hind A)
    _ ≤ (1 - densityRate + densityRate * s ^ 2) ^ N / (s ^ 2) ^ (m + 1) := hchern
    _ ≤ ((127 / 128) * s) ^ N / s ^ N := by
        apply div_le_div₀ (by positivity) (pow_le_pow_left₀ hbase0 hc N) (by positivity) hpow
    _ = (127 / 128 : ℝ) ^ N := by
        rw [mul_pow, mul_div_assoc, div_self (by positivity), mul_one]
    _ ≤ densityCapTail := hgeo

/-- Expected transfer error with the capped budget. -/
theorem tripleMask_capped_error_le
    (q r : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hr0 : ∀ e, 0 ≤ r e) (hr1 : ∀ e, r e ≤ 1)
    (hpq : ∀ e, densityRate + (1 - densityRate) * q e ≤ maskUnionRate)
    (V : Finset α) (F : Finset (Finset α)) (hF : ∀ R ∈ F, R ⊆ V)
    (hcard : (F.card : ℝ) ≤ Real.exp (residualExponent cappedThreshold * V.card))
    (hn : ruleKappa ≤ V.card)
    (error : Finset α → Finset α → Finset α → ℝ)
    (herror : ∀ D ⊆ V, ∀ C ⊆ V, ∀ T ⊆ V,
      error D C T ≤ (capturedMax F (D ∪ C) : ℝ) +
        (V.card : ℝ) * (if capBudget V.card < D.card / ruleKappa then 1 else 0)) :
    bitsExpectation (fun _ => densityRate) V
        (fun D => bitsExpectation q V (fun C => bitsExpectation r V (error D C))) ≤
      residualError * V.card := by
  have hp0 : ∀ _e : α, (0 : ℝ) ≤ densityRate := fun _ => by norm_num [densityRate]
  have hp1 : ∀ _e : α, densityRate ≤ (1 : ℝ) := fun _ => by norm_num [densityRate]
  have hpq0 : ∀ e, 0 ≤ densityRate + (1 - densityRate) * q e := by
    intro e
    exact add_nonneg (hp0 e) (mul_nonneg (sub_nonneg.mpr (hp1 e)) (hq0 e))
  have hΛ := residualExponent_nonneg_capped
  have hρ1 : maskUnionRate < 1 := by norm_num [maskUnionRate, densityRate, thinningRate]
  have hmax := bitsExpectation_capturedMax_le (fun e => densityRate + (1 - densityRate) * q e)
    maskUnionRate hpq0 hpq maskUnionRate_pos hρ1 V F hF _ hΛ hcard
  have htail := density_cap_tail_le V hn
  have hNr : (ruleKappa : ℝ) ≤ V.card := by exact_mod_cast hn
  have hk0 : (0 : ℝ) < ruleKappa := by exact_mod_cast ruleKappa_pos
  have hnum := capped_residual_numeric
  have hlpos : 0 < Real.log (1 / maskUnionRate) := Real.log_pos (by
    rw [lt_div_iff₀ maskUnionRate_pos]; linarith)
  calc
    _ ≤ bitsExpectation (fun _ => densityRate) V (fun D => bitsExpectation q V (fun C =>
          bitsExpectation r V (fun _T => (capturedMax F (D ∪ C) : ℝ) +
            (V.card : ℝ) * (if capBudget V.card < D.card / ruleKappa then 1 else 0)))) := by
      apply bitsExpectation_mono _ hp0 hp1
      intro D hD
      apply bitsExpectation_mono q hq0 hq1
      intro C hC
      exact bitsExpectation_mono r hr0 hr1 V (fun T hT => herror D hD C hC T hT)
    _ = bitsExpectation (fun e => densityRate + (1 - densityRate) * q e) V
          (fun S => (capturedMax F S : ℝ)) +
        (V.card : ℝ) * bitsExpectation (fun _ => densityRate) V
          (fun A => if capBudget V.card < A.card / ruleKappa then (1 : ℝ) else 0) := by
      simp_rw [bitsExpectation_const, bitsExpectation_add, bitsExpectation_const,
        bitsExpectation_mul_const]
      rw [bitsExpectation_union (fun _ => densityRate) q V (fun S => (capturedMax F S : ℝ))]
    _ ≤ (residualExponent cappedThreshold * V.card / Real.log (1 / maskUnionRate) +
          1 / (1 - maskUnionRate)) + (V.card : ℝ) * densityCapTail :=
      add_le_add hmax (mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _))
    _ ≤ residualError * V.card := by
      have hc0 : 0 ≤ 1 / (1 - maskUnionRate) := by
        have : 0 < 1 - maskUnionRate := by linarith
        positivity
      have h3 : 1 / (1 - maskUnionRate) ≤ 1 / (1 - maskUnionRate) / ruleKappa * V.card := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hk0]; nlinarith
      have hdiv : residualExponent cappedThreshold * V.card / Real.log (1 / maskUnionRate) =
          residualExponent cappedThreshold / Real.log (1 / maskUnionRate) * V.card := by ring
      rw [hdiv]
      nlinarith [Nat.cast_nonneg (α := ℝ) V.card]

end MatroidProphet

end OAI
