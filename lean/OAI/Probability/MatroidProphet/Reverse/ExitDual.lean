import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds
import OAI.Probability.MatroidProphet.ExitNumerics
import OAI.Probability.MatroidProphet.Constants

/-!
# Dual certificate for the squared exit mass

The squared exit mass is bounded below by duality against the constraints
`E ∑ 1{alive} h = 1` and `E ∑ 1{alive, h ≥ 2⁻ʲ} (1 - h) ≤ j log 2`.
The dual certificate is the step function `exitWeight` below together with the slope `1/2`.
-/

set_option linter.unusedSimpArgs false

namespace OAI

namespace MatroidProphet

open Finset

noncomputable section

/-- The concave profile `T x = x (1/2 - x) / (1 - x)` of the continuous certificate. -/
def exitProfile (x : ℝ) : ℝ := x * (1 / 2 - x) / (1 - x)

/-- Threshold of the `i`-th constraint: `2^-(i+2)`, for `i < 11`. -/
def exitThresholdAt (i : ℕ) : ℝ := ((2 : ℝ) ^ (i + 2))⁻¹

/-- Level of the certificate just below threshold `i`: `T(2^-(i+2))`; above `1/4` it is `429/5000`. -/
def exitLevel (i : ℕ) : ℝ := exitProfile (((2 : ℝ) ^ (i + 2))⁻¹)

/-- Jump of the certificate at threshold `i`. -/
def exitWeight (i : ℕ) : ℝ :=
  if i = 0 then 429 / 5000 - exitLevel 0
  else if i < 10 then exitLevel (i - 1) - exitLevel i
  else exitLevel 9

/-- The step certificate `W x = ∑ᵢ wᵢ 1{x ≥ 2^-(i+2)}`. -/
def exitCertificate (x : ℝ) : ℝ :=
  ∑ i ∈ range 11, exitWeight i * (if exitThresholdAt i ≤ x then 1 else 0)

lemma exitProfile_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1 / 4) :
    x / 2 - x ^ 2 ≤ (1 - x) * exitProfile y := by
  unfold exitProfile
  have hy1 : 0 < 1 - y := by linarith
  rw [mul_div_assoc', le_div_iff₀ hy1]
  have h1 : 0 ≤ y - x := by linarith
  have h2 : 0 ≤ 1 / 2 - x - y + x * y := by nlinarith
  nlinarith [mul_nonneg h1 h2]

lemma exitWeight_nonneg (i : ℕ) (hi : i < 11) : 0 ≤ exitWeight i := by
  unfold exitWeight exitLevel exitProfile
  interval_cases i <;> norm_num

/-- Pointwise dual inequality. -/
theorem exit_pointwise (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ x ^ 2 + (1 - x) * exitCertificate x +
      1 / 2 * (if x < ((2 : ℝ) ^ 12)⁻¹ then x else 0) := by
  have hW0 : 0 ≤ exitCertificate x := by
    unfold exitCertificate
    refine sum_nonneg fun i hi => mul_nonneg (exitWeight_nonneg i (mem_range.mp hi)) ?_
    split_ifs <;> norm_num
  by_cases hlow : x < ((2 : ℝ) ^ 12)⁻¹
  · rw [ite_eq_left hlow]
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - x) hW0, sq_nonneg x]
  rw [ite_eq_right hlow]
  push Not at hlow
  norm_num at hlow
  simp only [exitCertificate, exitThresholdAt, exitWeight, exitLevel, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num
  by_cases hb4 : (1 / 4 : ℝ) ≤ x
  ·
    simp only [show (1 / 4 : ℝ) ≤ x by linarith, show (1 / 8 : ℝ) ≤ x by linarith, show (1 / 16 : ℝ) ≤ x by linarith, show (1 / 32 : ℝ) ≤ x by linarith, show (1 / 64 : ℝ) ≤ x by linarith, show (1 / 128 : ℝ) ≤ x by linarith, show (1 / 256 : ℝ) ≤ x by linarith, show (1 / 512 : ℝ) ≤ x by linarith, show (1 / 1024 : ℝ) ≤ x by linarith, show (1 / 2048 : ℝ) ≤ x by linarith, show (1 / 4096 : ℝ) ≤ x by linarith, ite_true, ite_false, add_zero, zero_add]
    nlinarith [sq_nonneg (x - 293 / 1000)]
  push Not at hb4
  by_cases hb8 : (1 / 8 : ℝ) ≤ x
  ·
    simp only [show ¬ ((1 / 4 : ℝ) ≤ x) by linarith, show (1 / 8 : ℝ) ≤ x by linarith, show (1 / 16 : ℝ) ≤ x by linarith, show (1 / 32 : ℝ) ≤ x by linarith, show (1 / 64 : ℝ) ≤ x by linarith, show (1 / 128 : ℝ) ≤ x by linarith, show (1 / 256 : ℝ) ≤ x by linarith, show (1 / 512 : ℝ) ≤ x by linarith, show (1 / 1024 : ℝ) ≤ x by linarith, show (1 / 2048 : ℝ) ≤ x by linarith, show (1 / 4096 : ℝ) ≤ x by linarith, ite_true, ite_false, add_zero, zero_add]
    have key := exitProfile_mono hx0 (show x ≤ 1 / 4 by linarith) (by norm_num)
    linarith [key]
  push Not at hb8
  by_cases hb16 : (1 / 16 : ℝ) ≤ x
  ·
    simp only [show ¬ ((1 / 4 : ℝ) ≤ x) by linarith, show ¬ ((1 / 8 : ℝ) ≤ x) by linarith, show (1 / 16 : ℝ) ≤ x by linarith, show (1 / 32 : ℝ) ≤ x by linarith, show (1 / 64 : ℝ) ≤ x by linarith, show (1 / 128 : ℝ) ≤ x by linarith, show (1 / 256 : ℝ) ≤ x by linarith, show (1 / 512 : ℝ) ≤ x by linarith, show (1 / 1024 : ℝ) ≤ x by linarith, show (1 / 2048 : ℝ) ≤ x by linarith, show (1 / 4096 : ℝ) ≤ x by linarith, ite_true, ite_false, add_zero, zero_add]
    have key := exitProfile_mono hx0 (show x ≤ 1 / 8 by linarith) (by norm_num)
    linarith [key]
  push Not at hb16
  by_cases hb32 : (1 / 32 : ℝ) ≤ x
  ·
    simp only [show ¬ ((1 / 4 : ℝ) ≤ x) by linarith, show ¬ ((1 / 8 : ℝ) ≤ x) by linarith, show ¬ ((1 / 16 : ℝ) ≤ x) by linarith, show (1 / 32 : ℝ) ≤ x by linarith, show (1 / 64 : ℝ) ≤ x by linarith, show (1 / 128 : ℝ) ≤ x by linarith, show (1 / 256 : ℝ) ≤ x by linarith, show (1 / 512 : ℝ) ≤ x by linarith, show (1 / 1024 : ℝ) ≤ x by linarith, show (1 / 2048 : ℝ) ≤ x by linarith, show (1 / 4096 : ℝ) ≤ x by linarith, ite_true, ite_false, add_zero, zero_add]
    have key := exitProfile_mono hx0 (show x ≤ 1 / 16 by linarith) (by norm_num)
    linarith [key]
  push Not at hb32
  by_cases hb64 : (1 / 64 : ℝ) ≤ x
  ·
    simp only [show ¬ ((1 / 4 : ℝ) ≤ x) by linarith, show ¬ ((1 / 8 : ℝ) ≤ x) by linarith, show ¬ ((1 / 16 : ℝ) ≤ x) by linarith, show ¬ ((1 / 32 : ℝ) ≤ x) by linarith, show (1 / 64 : ℝ) ≤ x by linarith, show (1 / 128 : ℝ) ≤ x by linarith, show (1 / 256 : ℝ) ≤ x by linarith, show (1 / 512 : ℝ) ≤ x by linarith, show (1 / 1024 : ℝ) ≤ x by linarith, show (1 / 2048 : ℝ) ≤ x by linarith, show (1 / 4096 : ℝ) ≤ x by linarith, ite_true, ite_false, add_zero, zero_add]
    have key := exitProfile_mono hx0 (show x ≤ 1 / 32 by linarith) (by norm_num)
    linarith [key]
  push Not at hb64
  by_cases hb128 : (1 / 128 : ℝ) ≤ x
  ·
    simp only [show ¬ ((1 / 4 : ℝ) ≤ x) by linarith, show ¬ ((1 / 8 : ℝ) ≤ x) by linarith, show ¬ ((1 / 16 : ℝ) ≤ x) by linarith, show ¬ ((1 / 32 : ℝ) ≤ x) by linarith, show ¬ ((1 / 64 : ℝ) ≤ x) by linarith, show (1 / 128 : ℝ) ≤ x by linarith, show (1 / 256 : ℝ) ≤ x by linarith, show (1 / 512 : ℝ) ≤ x by linarith, show (1 / 1024 : ℝ) ≤ x by linarith, show (1 / 2048 : ℝ) ≤ x by linarith, show (1 / 4096 : ℝ) ≤ x by linarith, ite_true, ite_false, add_zero, zero_add]
    have key := exitProfile_mono hx0 (show x ≤ 1 / 64 by linarith) (by norm_num)
    linarith [key]
  push Not at hb128
  by_cases hb256 : (1 / 256 : ℝ) ≤ x
  ·
    simp only [show ¬ ((1 / 4 : ℝ) ≤ x) by linarith, show ¬ ((1 / 8 : ℝ) ≤ x) by linarith, show ¬ ((1 / 16 : ℝ) ≤ x) by linarith, show ¬ ((1 / 32 : ℝ) ≤ x) by linarith, show ¬ ((1 / 64 : ℝ) ≤ x) by linarith, show ¬ ((1 / 128 : ℝ) ≤ x) by linarith, show (1 / 256 : ℝ) ≤ x by linarith, show (1 / 512 : ℝ) ≤ x by linarith, show (1 / 1024 : ℝ) ≤ x by linarith, show (1 / 2048 : ℝ) ≤ x by linarith, show (1 / 4096 : ℝ) ≤ x by linarith, ite_true, ite_false, add_zero, zero_add]
    have key := exitProfile_mono hx0 (show x ≤ 1 / 128 by linarith) (by norm_num)
    linarith [key]
  push Not at hb256
  by_cases hb512 : (1 / 512 : ℝ) ≤ x
  ·
    simp only [show ¬ ((1 / 4 : ℝ) ≤ x) by linarith, show ¬ ((1 / 8 : ℝ) ≤ x) by linarith, show ¬ ((1 / 16 : ℝ) ≤ x) by linarith, show ¬ ((1 / 32 : ℝ) ≤ x) by linarith, show ¬ ((1 / 64 : ℝ) ≤ x) by linarith, show ¬ ((1 / 128 : ℝ) ≤ x) by linarith, show ¬ ((1 / 256 : ℝ) ≤ x) by linarith, show (1 / 512 : ℝ) ≤ x by linarith, show (1 / 1024 : ℝ) ≤ x by linarith, show (1 / 2048 : ℝ) ≤ x by linarith, show (1 / 4096 : ℝ) ≤ x by linarith, ite_true, ite_false, add_zero, zero_add]
    have key := exitProfile_mono hx0 (show x ≤ 1 / 256 by linarith) (by norm_num)
    linarith [key]
  push Not at hb512
  by_cases hb1024 : (1 / 1024 : ℝ) ≤ x
  ·
    simp only [show ¬ ((1 / 4 : ℝ) ≤ x) by linarith, show ¬ ((1 / 8 : ℝ) ≤ x) by linarith, show ¬ ((1 / 16 : ℝ) ≤ x) by linarith, show ¬ ((1 / 32 : ℝ) ≤ x) by linarith, show ¬ ((1 / 64 : ℝ) ≤ x) by linarith, show ¬ ((1 / 128 : ℝ) ≤ x) by linarith, show ¬ ((1 / 256 : ℝ) ≤ x) by linarith, show ¬ ((1 / 512 : ℝ) ≤ x) by linarith, show (1 / 1024 : ℝ) ≤ x by linarith, show (1 / 2048 : ℝ) ≤ x by linarith, show (1 / 4096 : ℝ) ≤ x by linarith, ite_true, ite_false, add_zero, zero_add]
    have key := exitProfile_mono hx0 (show x ≤ 1 / 512 by linarith) (by norm_num)
    linarith [key]
  push Not at hb1024
  by_cases hb2048 : (1 / 2048 : ℝ) ≤ x
  ·
    simp only [show ¬ ((1 / 4 : ℝ) ≤ x) by linarith, show ¬ ((1 / 8 : ℝ) ≤ x) by linarith, show ¬ ((1 / 16 : ℝ) ≤ x) by linarith, show ¬ ((1 / 32 : ℝ) ≤ x) by linarith, show ¬ ((1 / 64 : ℝ) ≤ x) by linarith, show ¬ ((1 / 128 : ℝ) ≤ x) by linarith, show ¬ ((1 / 256 : ℝ) ≤ x) by linarith, show ¬ ((1 / 512 : ℝ) ≤ x) by linarith, show ¬ ((1 / 1024 : ℝ) ≤ x) by linarith, show (1 / 2048 : ℝ) ≤ x by linarith, show (1 / 4096 : ℝ) ≤ x by linarith, ite_true, ite_false, add_zero, zero_add]
    have key := exitProfile_mono hx0 (show x ≤ 1 / 1024 by linarith) (by norm_num)
    linarith [key]
  push Not at hb2048
  by_cases hb4096 : (1 / 4096 : ℝ) ≤ x
  ·
    simp only [show ¬ ((1 / 4 : ℝ) ≤ x) by linarith, show ¬ ((1 / 8 : ℝ) ≤ x) by linarith, show ¬ ((1 / 16 : ℝ) ≤ x) by linarith, show ¬ ((1 / 32 : ℝ) ≤ x) by linarith, show ¬ ((1 / 64 : ℝ) ≤ x) by linarith, show ¬ ((1 / 128 : ℝ) ≤ x) by linarith, show ¬ ((1 / 256 : ℝ) ≤ x) by linarith, show ¬ ((1 / 512 : ℝ) ≤ x) by linarith, show ¬ ((1 / 1024 : ℝ) ≤ x) by linarith, show ¬ ((1 / 2048 : ℝ) ≤ x) by linarith, show (1 / 4096 : ℝ) ≤ x by linarith, ite_true, ite_false, add_zero, zero_add]
    have key := exitProfile_mono hx0 (show x ≤ 1 / 2048 by linarith) (by norm_num)
    linarith [key]
  push Not at hb4096
  linarith


/-- Numerical value of the dual objective. -/
theorem exit_dual_value :
    (∑ i ∈ range 11, exitWeight i * (((i : ℝ) + 2) * Real.log 2)) +
      1 / 2 * hazardTailPotential 12 ≤ 1 / 2 - exitMass := by
  have hlog := Real.log_two_lt_d9
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  simp only [exitWeight, exitLevel, exitProfile, Finset.sum_range_succ, Finset.sum_range_zero,
    hazardTailPotential, exitMass]
  norm_num
  nlinarith

end

end MatroidProphet

end OAI
