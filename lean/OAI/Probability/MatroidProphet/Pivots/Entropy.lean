import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace OAI

namespace MatroidProphet.Pivots

open Finset

noncomputable def binomialSum (n d : ℕ) : ℕ := ∑ k ∈ Iic d, n.choose k

lemma binomialSum_le_weighted (n d : ℕ) (κ : ℝ) (hκ : 1 ≤ κ) :
    (binomialSum n d : ℝ) ≤ κ ^ d * (1 + κ⁻¹) ^ n := by
  have hkpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have htrunc : (binomialSum n d : ℝ) = ∑ k ∈ Iic d ∩ Iic n, (n.choose k : ℝ) := by
    rw [binomialSum, Nat.cast_sum]
    apply (sum_subset inter_subset_left ?_).symm
    intro k hkd hnot
    have hnk : n < k := by simpa only [mem_inter, hkd, true_and, mem_Iic, not_le] using hnot
    simp [Nat.choose_eq_zero_of_lt hnk]
  have hp (k : ℕ) (hkd : k ≤ d) : 1 ≤ κ ^ d * (κ⁻¹) ^ k := by
    rw [inv_pow, ← div_eq_mul_inv]
    exact (one_le_div₀ (pow_pos hkpos k)).2 (pow_le_pow_right₀ hκ hkd)
  calc
    (binomialSum n d : ℝ) = ∑ k ∈ Iic d ∩ Iic n, (n.choose k : ℝ) := htrunc
    _ ≤ ∑ k ∈ Iic d ∩ Iic n, κ ^ d * ((κ⁻¹) ^ k * (n.choose k : ℝ)) := by
      apply sum_le_sum
      intro k hk
      have h := mul_le_mul_of_nonneg_right (hp k (mem_Iic.mp (mem_inter.mp hk).1))
        (Nat.cast_nonneg (n.choose k) : (0 : ℝ) ≤ n.choose k)
      simpa only [one_mul, mul_assoc] using h
    _ ≤ ∑ k ∈ Iic n, κ ^ d * ((κ⁻¹) ^ k * (n.choose k : ℝ)) :=
      sum_le_sum_of_subset_of_nonneg inter_subset_right (by intros; positivity)
    _ = κ ^ d * (1 + κ⁻¹) ^ n := by
      rw [← mul_sum, add_comm 1, add_pow, Nat.range_succ_eq_Iic]
      simp

lemma binomialSum_le_exp (n d : ℕ) (κ : ℝ) (hκ : 1 ≤ κ) :
    (binomialSum n d : ℝ) ≤ Real.exp ((d : ℝ) * Real.log κ + (n : ℝ) / κ) := by
  have hkpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hone : 1 + κ⁻¹ ≤ Real.exp κ⁻¹ := by simpa [add_comm] using Real.add_one_le_exp κ⁻¹
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + κ⁻¹) hone n
  calc
    (binomialSum n d : ℝ) ≤ κ ^ d * (1 + κ⁻¹) ^ n := binomialSum_le_weighted n d κ hκ
    _ ≤ κ ^ d * (Real.exp κ⁻¹) ^ n := mul_le_mul_of_nonneg_left hpow (pow_nonneg hkpos.le d)
    _ = Real.exp ((d : ℝ) * Real.log κ + (n : ℝ) / κ) := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hkpos, div_eq_mul_inv, Real.exp_nat_mul]

/-- Exponent of the sharpened residual-family count at density charge `κ`. -/
noncomputable def residualExponent (κ : ℝ) : ℝ :=
  (3 * (1 + Real.log κ) + 2 * (1 + Real.log (κ / 2)) + 3 * Real.log 4) / κ

/-- Entropy bound for the sharpened count. -/
theorem residual_sharp_product_le_exp (n q : ℕ) (κ : ℝ) (hκ : 2 ≤ κ)
    (hq : (q : ℝ) ≤ (n : ℝ) / κ) :
    (((binomialSum n q) ^ 2 * (4 ^ q * binomialSum n q) *
        (4 ^ (2 * q) * binomialSum n (2 * q)) : ℕ) : ℝ) ≤
      Real.exp (residualExponent κ * n) := by
  have hkpos : 0 < κ := by linarith
  have hk1 : 1 ≤ κ := by linarith
  have hk2 : 1 ≤ κ / 2 := by linarith
  have hlogk : 0 ≤ Real.log κ := Real.log_nonneg hk1
  have hlogk2 : 0 ≤ Real.log (κ / 2) := Real.log_nonneg hk2
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hn : 0 ≤ (n : ℝ) / κ := by positivity
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h1 := binomialSum_le_exp n q κ hk1
  have h2 := binomialSum_le_exp n (2 * q) (κ / 2) hk2
  have h4 : ((4 : ℕ) : ℝ) ^ q = Real.exp ((q : ℝ) * Real.log 4) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_num
  have h4' : ((4 : ℕ) : ℝ) ^ (2 * q) = Real.exp (((2 * q : ℕ) : ℝ) * Real.log 4) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_num
  push_cast
  have hb1 : (0 : ℝ) ≤ binomialSum n q := Nat.cast_nonneg _
  have hb2 : (0 : ℝ) ≤ binomialSum n (2 * q) := Nat.cast_nonneg _
  calc
    ((binomialSum n q : ℝ) ^ 2 * (4 ^ q * binomialSum n q) * (4 ^ (2 * q) * binomialSum n (2 * q)))
        ≤ Real.exp ((q : ℝ) * Real.log κ + (n : ℝ) / κ) ^ 2 *
            (Real.exp ((q : ℝ) * Real.log 4) * Real.exp ((q : ℝ) * Real.log κ + (n : ℝ) / κ)) *
            (Real.exp (((2 * q : ℕ) : ℝ) * Real.log 4) *
              Real.exp (((2 * q : ℕ) : ℝ) * Real.log (κ / 2) + (n : ℝ) / (κ / 2))) := by
          have e4 : (4 : ℝ) ^ q = Real.exp ((q : ℝ) * Real.log 4) := by exact_mod_cast h4
          have e4' : (4 : ℝ) ^ (2 * q) = Real.exp (((2 * q : ℕ) : ℝ) * Real.log 4) := by
            exact_mod_cast h4'
          rw [e4, e4']
          gcongr
    _ = Real.exp ((q : ℝ) * (3 * Real.log κ + 3 * Real.log 4 + 2 * Real.log (κ / 2)) +
          (n : ℝ) / κ * 5) := by
          rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1
          push_cast
          field_simp
          ring
    _ ≤ Real.exp (residualExponent κ * n) := by
          apply Real.exp_le_exp.mpr
          unfold residualExponent
          have hqk : (q : ℝ) * (3 * Real.log κ + 3 * Real.log 4 + 2 * Real.log (κ / 2)) ≤
              (n : ℝ) / κ * (3 * Real.log κ + 3 * Real.log 4 + 2 * Real.log (κ / 2)) :=
            mul_le_mul_of_nonneg_right hq (by positivity)
          have hrw : (3 * (1 + Real.log κ) + 2 * (1 + Real.log (κ / 2)) + 3 * Real.log 4) / κ * n =
              (n : ℝ) / κ * (3 * Real.log κ + 3 * Real.log 4 + 2 * Real.log (κ / 2)) +
                (n : ℝ) / κ * 5 := by
            field_simp
            ring
          rw [hrw]
          nlinarith

/-- The sharpened residual exponent at `κ = 2^12`. -/
theorem residualExponent_charge :
    residualExponent (2 ^ 12) = (5 + 64 * Real.log 2) / 4096 := by
  unfold residualExponent
  have h1 : Real.log ((2 : ℝ) ^ 12) = 12 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have h2 : Real.log ((2 : ℝ) ^ 12 / 2) = 11 * Real.log 2 := by
    rw [show ((2 : ℝ) ^ 12 / 2) = 2 ^ 11 by norm_num, Real.log_pow]; norm_num
  have h3 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [h1, h2, h3]
  norm_num
  ring


end MatroidProphet.Pivots

end OAI
