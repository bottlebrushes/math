import OAI.Probability.MatroidProphet.Residual.CappedTail
import OAI.Probability.MatroidProphet.Residual.Constants
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Expected transfer error with a capped generator budget

For a group of `N ≥ 2^12` labels, the capped budget `capBudget N = ⌊9N/16⌋ / 2^12` admits a
residual family of size `exp(Λ N)` with `Λ = residualExponent (2^16/9)`.  The transfer gap is at
most the largest captured residual plus `N` on the event that the density sample has more than
`9N/16` labels.  The first term has expectation `Λ N / log 2 + 3` (layer cake); the second is a
Chernoff tail at density rate `31/64`.
-/

namespace OAI

namespace MatroidProphet
open Finset Pivots
variable {α : Type*} [DecidableEq α]

set_option linter.unusedSectionVars false

/-- Real budget denominator: `capBudget N ≤ N / cappedThreshold`. -/
noncomputable def cappedThreshold : ℝ := 2 ^ 16 / 9

lemma capBudget_le (N : ℕ) : (capBudget N : ℝ) ≤ (N : ℝ) / cappedThreshold := by
  unfold capBudget cappedThreshold
  have h1 : ((9 * N / 16 / 2 ^ 12 : ℕ) : ℝ) * 2 ^ 12 ≤ (9 * N / 16 : ℕ) := by
    exact_mod_cast Nat.div_mul_le_self _ _
  have h2 : ((9 * N / 16 : ℕ) : ℝ) * 16 ≤ ((9 * N : ℕ) : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self _ _
  push_cast at h2
  rw [le_div_iff₀ (by norm_num)]
  nlinarith

lemma two_le_cappedThreshold : (2 : ℝ) ≤ cappedThreshold := by
  norm_num [cappedThreshold]

lemma capped_exponent_div_log_le :
    residualExponent cappedThreshold / Real.log 2 ≤ (5 / Real.log 2 + 69) * (9 / 2 ^ 16) := by
  have hl := Real.log_two_gt_d9
  have hlpos : 0 < Real.log 2 := by linarith
  have hk : (0 : ℝ) < cappedThreshold := by norm_num [cappedThreshold]
  have hL1 : Real.log cappedThreshold ≤ 13 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    apply Real.log_le_log hk
    norm_num [cappedThreshold]
  have hL2 : Real.log (cappedThreshold / 2) ≤ 12 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    apply Real.log_le_log (by positivity)
    norm_num [cappedThreshold]
  have hL4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  unfold residualExponent
  rw [div_div, div_le_iff₀ (by positivity)]
  have hkv : cappedThreshold = 2 ^ 16 / 9 := rfl
  rw [hkv] at hL1 hL2 ⊢
  field_simp
  nlinarith

lemma capped_residual_numeric :
    residualExponent cappedThreshold / Real.log 2 + 3 / 2 ^ 12 + (3 / 8 : ℝ) ^ 16 ≤
      residualError := by
  have h := capped_exponent_div_log_le
  have hl := Real.log_two_gt_d9
  have hinv : 5 / Real.log 2 ≤ 5 / 0.6931471803 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hl.le
  unfold residualError
  nlinarith

/-- The Chernoff tail of a density sample above `9N/16`. -/
theorem density_cap_tail_le (V : Finset α) (hN : 2 ^ 12 ≤ V.card) :
    bitsExpectation (fun _ => densityRate) V
        (fun A => if capBudget V.card < A.card / 2 ^ 12 then (1 : ℝ) else 0) ≤
      (3 / 8 : ℝ) ^ 16 := by
  set N := V.card
  set m := 9 * N / 16
  set s : ℝ := 129 / 128
  have hp0 : (0 : ℝ) ≤ densityRate := by norm_num [densityRate]
  have hp1 : densityRate ≤ (1 : ℝ) := by norm_num [densityRate]
  have hr : (1 : ℝ) ≤ s ^ 16 := one_le_pow₀ (by norm_num [s])
  have hind (A : Finset α) : (if capBudget N < A.card / 2 ^ 12 then (1 : ℝ) else 0) ≤
      (if m < A.card then (1 : ℝ) else 0) := by
    by_cases h : capBudget N < A.card / 2 ^ 12
    · have hm : m < A.card := by
        by_contra hle
        push_neg at hle
        exact absurd (Nat.div_le_div_right (c := 2 ^ 12) hle) (by unfold capBudget at h; omega)
      simp only [h, hm, ite_true, le_refl]
    · simp only [h, ite_false]; split_ifs <;> norm_num
  have hchern := bitsExpectation_card_gt_le densityRate (s ^ 16) hp0 hp1 hr V m
  have hc : (1 - densityRate + densityRate * s ^ 16) ≤ (255 / 256) * s ^ 9 := by
    norm_num [densityRate, s]
  have hexp : 9 * N ≤ 16 * (m + 1) := by omega
  have hpow : (s ^ 9) ^ N ≤ (s ^ 16) ^ (m + 1) := by
    rw [← pow_mul, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num [s]) (by linarith)
  have hspos : 0 < s ^ 9 := by positivity
  have hbase0 : 0 ≤ 1 - densityRate + densityRate * s ^ 16 := by
    have := pow_nonneg (show (0 : ℝ) ≤ s by norm_num [s]) 16
    nlinarith
  have hgeo : (255 / 256 : ℝ) ^ N ≤ (3 / 8) ^ 16 := by
    calc (255 / 256 : ℝ) ^ N ≤ (255 / 256) ^ (2 ^ 12) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hN
      _ = ((255 / 256 : ℝ) ^ 256) ^ 16 := by rw [← pow_mul]; norm_num
      _ ≤ (3 / 8) ^ 16 := pow_le_pow_left₀ (by positivity) (by norm_num) 16
  calc _ ≤ bitsExpectation (fun _ => densityRate) V (fun A => if m < A.card then (1 : ℝ) else 0) :=
        bitsExpectation_mono _ (fun _ => hp0) (fun _ => hp1) V (fun A _ => hind A)
    _ ≤ (1 - densityRate + densityRate * s ^ 16) ^ N / (s ^ 16) ^ (m + 1) := hchern
    _ ≤ ((255 / 256) * s ^ 9) ^ N / (s ^ 9) ^ N := by
        apply div_le_div₀ (by positivity) (pow_le_pow_left₀ hbase0 hc N) (by positivity) hpow
    _ = (255 / 256 : ℝ) ^ N := by
        rw [mul_pow, mul_div_assoc, div_self (by positivity), mul_one]
    _ ≤ (3 / 8) ^ 16 := hgeo

/-- Expected transfer error with the capped budget. -/
theorem tripleMask_capped_error_le
    (q r : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (hr0 : ∀ e, 0 ≤ r e) (hr1 : ∀ e, r e ≤ 1)
    (hpq : ∀ e, densityRate + (1 - densityRate) * q e ≤ 1 / 2)
    (V : Finset α) (F : Finset (Finset α)) (hF : ∀ R ∈ F, R ⊆ V)
    (hcard : (F.card : ℝ) ≤ Real.exp (residualExponent cappedThreshold * V.card))
    (hn : 2 ^ 12 ≤ V.card)
    (error : Finset α → Finset α → Finset α → ℝ)
    (herror : ∀ D ⊆ V, ∀ C ⊆ V, ∀ T ⊆ V,
      error D C T ≤ (capturedMax F (D ∪ C) : ℝ) +
        (V.card : ℝ) * (if capBudget V.card < D.card / 2 ^ 12 then 1 else 0)) :
    bitsExpectation (fun _ => densityRate) V
        (fun D => bitsExpectation q V (fun C => bitsExpectation r V (error D C))) ≤
      residualError * V.card := by
  have hp0 : ∀ _e : α, (0 : ℝ) ≤ densityRate := fun _ => by norm_num [densityRate]
  have hp1 : ∀ _e : α, densityRate ≤ (1 : ℝ) := fun _ => by norm_num [densityRate]
  have hpq0 : ∀ e, 0 ≤ densityRate + (1 - densityRate) * q e := by
    intro e
    exact add_nonneg (hp0 e) (mul_nonneg (sub_nonneg.mpr (hp1 e)) (hq0 e))
  have hΛ : 0 ≤ residualExponent cappedThreshold := by
    unfold residualExponent cappedThreshold
    have h1 : 0 ≤ Real.log ((2 : ℝ) ^ 16 / 9) := Real.log_nonneg (by norm_num)
    have h2 : 0 ≤ Real.log ((2 : ℝ) ^ 16 / 9 / 2) := Real.log_nonneg (by norm_num)
    have h3 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
    positivity
  have hmax := bitsExpectation_capturedMax_le (fun e => densityRate + (1 - densityRate) * q e)
    hpq0 hpq V F hF _ hΛ hcard
  have htail := density_cap_tail_le V hn
  have hNr : (2 : ℝ) ^ 12 ≤ V.card := by exact_mod_cast hn
  have hnum := capped_residual_numeric
  have hlpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    _ ≤ bitsExpectation (fun _ => densityRate) V (fun D => bitsExpectation q V (fun C =>
          bitsExpectation r V (fun _T => (capturedMax F (D ∪ C) : ℝ) +
            (V.card : ℝ) * (if capBudget V.card < D.card / 2 ^ 12 then 1 else 0)))) := by
      apply bitsExpectation_mono _ hp0 hp1
      intro D hD
      apply bitsExpectation_mono q hq0 hq1
      intro C hC
      exact bitsExpectation_mono r hr0 hr1 V (fun T hT => herror D hD C hC T hT)
    _ = bitsExpectation (fun e => densityRate + (1 - densityRate) * q e) V
          (fun S => (capturedMax F S : ℝ)) +
        (V.card : ℝ) * bitsExpectation (fun _ => densityRate) V
          (fun A => if capBudget V.card < A.card / 2 ^ 12 then (1 : ℝ) else 0) := by
      simp_rw [bitsExpectation_const, bitsExpectation_add, bitsExpectation_const,
        bitsExpectation_mul_const]
      rw [bitsExpectation_union (fun _ => densityRate) q V (fun S => (capturedMax F S : ℝ))]
    _ ≤ (residualExponent cappedThreshold * V.card / Real.log 2 + 3) +
        (V.card : ℝ) * (3 / 8) ^ 16 :=
      add_le_add hmax (mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg _))
    _ ≤ residualError * V.card := by
      have h3 : (3 : ℝ) ≤ 3 / 2 ^ 12 * V.card := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]; nlinarith
      have hdiv : residualExponent cappedThreshold * V.card / Real.log 2 =
          residualExponent cappedThreshold / Real.log 2 * V.card := by ring
      rw [hdiv]
      nlinarith [Nat.cast_nonneg (α := ℝ) V.card]

end MatroidProphet

end OAI
