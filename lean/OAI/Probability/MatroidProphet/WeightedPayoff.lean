import OAI.Probability.MatroidProphet.WeightedAccounting
import OAI.Probability.MatroidProphet.Residual.Probability
import Mathlib.Tactic.Positivity

namespace OAI

namespace MatroidProphet

open Finset

lemma weighted_group_payoff (B t κ γ a b ε c : ℝ)
    (hB : 1 < B) (ht : 0 ≤ t) (hκ : 0 < κ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (herr : a + b / (B - 1) ≤ ε)
    (levels analyzed : Finset ℤ) (hsub : analyzed ⊆ levels)
    (N Y Λ : ℤ → ℝ) (hN : ∀ i ∈ levels, 0 ≤ N i)
    (hgroup : ∀ i ∈ analyzed,
      t / κ * (γ * Y i - a * N i - b * ∑ l ∈ levels with i < l, N l) ≤ Λ i) :
    c * (t / κ) * (γ * ∑ i ∈ analyzed, B ^ i * Y i - ε * ∑ i ∈ levels, B ^ i * N i) ≤
      c * ∑ i ∈ analyzed, B ^ i * Λ i := by
  have hB0 : 0 < B := zero_lt_one.trans hB
  have htotal : 0 ≤ ∑ i ∈ levels, B ^ i * N i :=
    Finset.sum_nonneg fun i hi => mul_nonneg (zpow_pos hB0 i).le (hN i hi)
  have hNsum : (∑ i ∈ analyzed, B ^ i * N i) ≤ ∑ i ∈ levels, B ^ i * N i :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ =>
      mul_nonneg (zpow_pos hB0 i).le (hN i hi))
  have hcost := higher_weight_cost B hB levels analyzed N hN
  have herrors : a * (∑ i ∈ analyzed, B ^ i * N i) +
      b * (∑ i ∈ analyzed, B ^ i * ∑ l ∈ levels with i < l, N l) ≤
      ε * ∑ i ∈ levels, B ^ i * N i := by
    calc
      _ ≤ a * (∑ i ∈ levels, B ^ i * N i) +
          b * ((∑ i ∈ levels, B ^ i * N i) / (B - 1)) :=
        add_le_add (mul_le_mul_of_nonneg_left hNsum ha) (mul_le_mul_of_nonneg_left hcost hb)
      _ = (a + b / (B - 1)) * ∑ i ∈ levels, B ^ i * N i := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right herr htotal
  have hsum : (∑ i ∈ analyzed,
      B ^ i * (t / κ * (γ * Y i - a * N i - b * ∑ l ∈ levels with i < l, N l))) ≤
      ∑ i ∈ analyzed, B ^ i * Λ i :=
    Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hgroup i hi) (zpow_pos hB0 i).le
  have heq : (∑ i ∈ analyzed,
      B ^ i * (t / κ * (γ * Y i - a * N i - b * ∑ l ∈ levels with i < l, N l))) =
      t / κ * (γ * (∑ i ∈ analyzed, B ^ i * Y i) -
        (a * (∑ i ∈ analyzed, B ^ i * N i) +
          b * (∑ i ∈ analyzed, B ^ i * ∑ l ∈ levels with i < l, N l))) := by
    have hi (i : ℤ) : B ^ i * (t / κ * (γ * Y i - a * N i -
        b * ∑ l ∈ levels with i < l, N l)) =
        (t / κ * γ) * (B ^ i * Y i) - (t / κ * a) * (B ^ i * N i) -
          (t / κ * b) * (B ^ i * ∑ l ∈ levels with i < l, N l) := by ring
    simp_rw [hi]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  rw [heq] at hsum
  have hbudget := mul_le_mul_of_nonneg_left
    (sub_le_sub_left herrors (γ * ∑ i ∈ analyzed, B ^ i * Y i)) (div_nonneg ht hκ.le)
  have hresult := hbudget.trans hsum
  calc
    _ = c * (t / κ *
        (γ * ∑ i ∈ analyzed, B ^ i * Y i - ε * ∑ i ∈ levels, B ^ i * N i)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hresult hc

lemma source_weighted_group_payoff (levels analyzed : Finset ℤ) (hsub : analyzed ⊆ levels)
    (N Y Λ : ℤ → ℝ) (hN : ∀ i ∈ levels, 0 ≤ N i)
    (hgroup : ∀ i ∈ analyzed,
      thinningRate / densityThreshold *
        (retainedFraction * Y i - (transferError + thinningRate * densityThreshold) * N i -
          (thinningRate * densityThreshold + densityRate) * ∑ l ∈ levels with i < l, N l) ≤
        Λ i) :
    (1 - 1 / weightBase) * (thinningRate / densityThreshold) *
      (retainedFraction * ∑ i ∈ analyzed, weightBase ^ i * Y i -
        payoffError * ∑ i ∈ levels, weightBase ^ i * N i) ≤
      (1 - 1 / weightBase) * ∑ i ∈ analyzed, weightBase ^ i * Λ i := by
  apply weighted_group_payoff weightBase thinningRate densityThreshold retainedFraction
    (transferError + thinningRate * densityThreshold)
    (thinningRate * densityThreshold + densityRate) payoffError (1 - 1 / weightBase)
    (by norm_num [weightBase]) constants_positive.2.2.1.le constants_positive.2.1
  · norm_num [transferError, thinningRate, densityThreshold]
  · norm_num [thinningRate, densityThreshold, densityRate]
  · norm_num [weightBase]
  · exact payoffError_ge
  · exact hsub
  · exact hN
  · exact hgroup

lemma sum_zpow_le_ratio_of_bound (B : ℝ) (hB : 1 < B) (levels : Finset ℤ)
    (m : ℝ) (hm : 0 ≤ m) (hbound : ∀ i ∈ levels, B ^ i ≤ m) :
    (∑ i ∈ levels, B ^ i) ≤ B / (B - 1) * m := by
  classical
  have hr : 0 ≤ B / (B - 1) := div_nonneg (by linarith) (by linarith)
  by_cases hn : levels.Nonempty
  · have h := sum_zpow_le_ratio B hB levels (levels.max' hn)
      (fun i hi => levels.le_max' i hi)
    exact h.trans (mul_le_mul_of_nonneg_left (hbound _ (levels.max'_mem hn)) hr)
  · have he : levels = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, Finset.sum_empty]
    positivity

lemma small_group_mass_bound (B κ m : ℝ) (hB : 1 < B) (hκ : 0 ≤ κ) (hm : 0 ≤ m)
    (levels : Finset ℤ) (Y : ℤ → ℝ) (hY : ∀ i ∈ levels, Y i ≤ κ)
    (hbound : ∀ i ∈ levels, B ^ i ≤ m) :
    (∑ i ∈ levels, B ^ i * Y i) ≤ κ * (B / (B - 1)) * m := by
  have hB0 : 0 < B := lt_trans zero_lt_one hB
  calc
    _ ≤ ∑ i ∈ levels, B ^ i * κ :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hY i hi) (zpow_pos hB0 i).le
    _ = κ * ∑ i ∈ levels, B ^ i := by rw [← Finset.sum_mul]; ring
    _ ≤ κ * (B / (B - 1) * m) := mul_le_mul_of_nonneg_left
      (sum_zpow_le_ratio_of_bound B hB levels m hm hbound) hκ
    _ = _ := by ring

lemma bitsExpectation_sub {α : Type*} [DecidableEq α] (q : α → ℝ) (V : Finset α)
    (f g : Finset α → ℝ) :
    bitsExpectation q V (fun H => f H - g H) = bitsExpectation q V f - bitsExpectation q V g := by
  simp only [bitsExpectation, mul_sub, Finset.sum_sub_distrib]

lemma main_branch_from_filter {α : Type*} [DecidableEq α] (V : Finset α)
    (bigY allY massU payoff : Finset α → ℝ) (W m : ℝ)
    (hW : 0 ≤ W) (hm : m ≤ smallThreshold * W)
    (hY : bitsExpectation (fun _ => filterRate) V allY = (1 - filterRate) * W)
    (hU : filterRate * bitsExpectation (fun _ => filterRate) V massU ≤ (1 - filterRate) * W)
    (hsmall : ∀ H ⊆ V, allY H ≤ bigY H + densityThreshold * (weightBase / (weightBase - 1)) * m)
    (hpay : ∀ H ⊆ V, (1 - 1 / weightBase) * (thinningRate / densityThreshold) *
      (retainedFraction * bigY H - payoffError * massU H) ≤ payoff H) :
    mainFraction * W ≤ bitsExpectation (fun _ => filterRate) V payoff := by
  let q : α → ℝ := fun _ => filterRate
  have hr := rates_mem
  have hq0 : ∀ e, 0 ≤ q e := fun _ => hr.1.le
  have hq1 : ∀ e, q e ≤ 1 := fun _ => hr.2.1.le
  have hybig := bitsExpectation_mono q hq0 hq1 V hsmall
  rw [bitsExpectation_add, bitsExpectation_const, hY] at hybig
  have hk : 0 < densityThreshold := constants_positive.2.1
  have hbig : (1 - filterRate) * (1 - smallFraction * (weightBase / (weightBase - 1))) * W ≤
      bitsExpectation q V bigY := by
    have hθ : densityThreshold * (weightBase / (weightBase - 1)) * m ≤
        (1 - filterRate) * smallFraction * (weightBase / (weightBase - 1)) * W := by
      have hc : 0 ≤ densityThreshold * (weightBase / (weightBase - 1)) := by
        norm_num [densityThreshold, weightBase]
      have := mul_le_mul_of_nonneg_left hm hc
      have he : densityThreshold * (weightBase / (weightBase - 1)) * (smallThreshold * W) =
          (1 - filterRate) * smallFraction * (weightBase / (weightBase - 1)) * W := by
        unfold smallThreshold; field_simp
      linarith
    nlinarith
  have hmass : bitsExpectation q V massU ≤ (1 - filterRate) / filterRate * W := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hr.1]
    linarith [hU]
  have hpaid := bitsExpectation_mono q hq0 hq1 V hpay
  rw [bitsExpectation_mul_const, bitsExpectation_sub,
    bitsExpectation_mul_const, bitsExpectation_mul_const] at hpaid
  have hinner : (1 - filterRate) *
      (retainedFraction * (1 - smallFraction * (weightBase / (weightBase - 1))) -
        payoffError / filterRate) * W ≤
      retainedFraction * bitsExpectation q V bigY - payoffError * bitsExpectation q V massU := by
    have hγ : 0 ≤ retainedFraction := constants_positive.2.2.2.2.le
    have he : 0 ≤ payoffError := by norm_num [payoffError]
    have h1 := mul_le_mul_of_nonneg_left hbig hγ
    have h2 := mul_le_mul_of_nonneg_left hmass he
    have he2 : payoffError * ((1 - filterRate) / filterRate * W) =
        (1 - filterRate) * (payoffError / filterRate) * W := by
      field_simp
    nlinarith
  have hscale : 0 ≤ (1 - 1 / weightBase) * (thinningRate / densityThreshold) := by
    norm_num [weightBase, thinningRate, densityThreshold]
  have hscaled := mul_le_mul_of_nonneg_left hinner hscale
  have hfinal := hscaled.trans hpaid
  have he : (1 - 1 / weightBase) * (thinningRate / densityThreshold) * ((1 - filterRate) *
      (retainedFraction * (1 - smallFraction * (weightBase / (weightBase - 1))) -
        payoffError / filterRate) * W) = mainFraction * W := by
    unfold mainFraction; ring
  rw [he] at hfinal
  exact hfinal

end MatroidProphet

end OAI
