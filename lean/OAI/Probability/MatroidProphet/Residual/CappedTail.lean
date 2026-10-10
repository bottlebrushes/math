import OAI.Probability.MatroidProphet.Residual.Capped
import OAI.Probability.MatroidProphet.Residual.Tail

/-!
# Expected captured residual and the density-sample cap

* Layer cake: the largest captured residual has expectation at most `Λ n / log 2 + 3` when the
  family has at most `exp(Λ n)` members and the mask rate is at most `1/2`.
* Chernoff: a Bernoulli sample exceeds `m` with probability at most
  `(1 - p + p r)^n / r^(m+1)` for every `r ≥ 1`.
-/

namespace OAI

namespace MatroidProphet

open Finset

variable {α : Type*} [DecidableEq α]

set_option linter.unusedSectionVars false

lemma capturedMax_le_sum (F : Finset (Finset α)) (V S : Finset α) (hF : ∀ R ∈ F, R ⊆ V) :
    (capturedMax F S : ℝ) ≤ ∑ x ∈ range V.card, residualBadIndicator F x S := by
  classical
  have hmdef : capturedMax F S = (F.filter (fun R => R ⊆ S)).sup Finset.card := by
    unfold capturedMax; congr
  set m := capturedMax F S
  have hm : m ≤ V.card := by
    rw [hmdef]
    apply Finset.sup_le
    intro R hR
    exact Finset.card_le_card (hF R (Finset.mem_filter.mp hR).1)
  have hpoint (x : ℕ) (hx : x < m) : residualBadIndicator F x S = 1 := by
    have hpos : 0 < m := lt_of_le_of_lt (Nat.zero_le x) hx
    have hne : (F.filter (fun R => R ⊆ S)).Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      rw [hmdef, hne] at hpos
      simp at hpos
    obtain ⟨R, hR, hcard⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
    have hR' := Finset.mem_filter.mp hR
    unfold residualBadIndicator
    rw [ite_eq_left_iff.mpr]
    · intro hn; exact absurd ⟨R, hR'.1, by
        have : x < R.card := by rw [← hcard, ← hmdef]; exact hx
        exact_mod_cast this, hR'.2⟩ hn
  calc (m : ℝ) = ∑ x ∈ range m, (1 : ℝ) := by simp
    _ = ∑ x ∈ range m, residualBadIndicator F x S :=
        Finset.sum_congr rfl (fun x hx => (hpoint x (mem_range.mp hx)).symm)
    _ ≤ ∑ x ∈ range V.card, residualBadIndicator F x S := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hm)
        intro x _ _
        unfold residualBadIndicator
        split_ifs <;> norm_num

lemma residualBadIndicator_le_one (F : Finset (Finset α)) (t : ℝ) (S : Finset α) :
    residualBadIndicator F t S ≤ 1 := by
  unfold residualBadIndicator; split_ifs <;> norm_num

/-- Geometric tail sum. -/
lemma sum_min_geometric (c : ℝ) (hc : 0 ≤ c) (X N : ℕ) :
    (∑ x ∈ range N, min 1 (c * (1 / 2 : ℝ) ^ x)) ≤ X + 2 * c * (1 / 2 : ℝ) ^ X := by
  induction N with
  | zero => simp; positivity
  | succ N ih =>
    rw [sum_range_succ]
    by_cases hN : N < X
    · have h1 : min 1 (c * (1 / 2 : ℝ) ^ N) ≤ 1 := min_le_left _ _
      -- the first X terms contribute at most one each
      have hsplit : (∑ x ∈ range (N+1), min 1 (c * (1 / 2 : ℝ) ^ x)) ≤ (N + 1 : ℕ) := by
        calc (∑ x ∈ range (N+1), min 1 (c * (1 / 2 : ℝ) ^ x)) ≤ ∑ x ∈ range (N+1), (1 : ℝ) :=
              sum_le_sum (fun x _ => min_le_left _ _)
          _ = (N + 1 : ℕ) := by simp
      rw [← sum_range_succ]
      have hX : ((N + 1 : ℕ) : ℝ) ≤ X := by exact_mod_cast hN
      have : 0 ≤ 2 * c * (1 / 2 : ℝ) ^ X := by positivity
      linarith
    · -- for N ≥ X, add the geometric term
      have hgeo : (∑ x ∈ range (N+1), min 1 (c * (1 / 2 : ℝ) ^ x)) ≤
          X + 2 * c * (1 / 2 : ℝ) ^ X * (1 - (1 / 2 : ℝ) ^ (N + 1 - X)) := by
        have hb : ∀ M : ℕ, (∑ x ∈ range (X + M), min 1 (c * (1 / 2 : ℝ) ^ x)) ≤
            X + 2 * c * (1 / 2 : ℝ) ^ X * (1 - (1 / 2 : ℝ) ^ M) := by
          intro M
          induction M with
          | zero =>
            simp only [add_zero, pow_zero, sub_self, mul_zero]
            calc (∑ x ∈ range X, min 1 (c * (1 / 2 : ℝ) ^ x)) ≤ ∑ x ∈ range X, (1 : ℝ) :=
                  sum_le_sum (fun x _ => min_le_left _ _)
              _ = X := by simp
          | succ M ihM =>
            rw [← add_assoc, sum_range_succ]
            have hm : min 1 (c * (1 / 2 : ℝ) ^ (X + M)) ≤ c * (1 / 2 : ℝ) ^ (X + M) :=
              min_le_right _ _
            have he : c * (1 / 2 : ℝ) ^ (X + M) =
                2 * c * (1 / 2 : ℝ) ^ X * ((1 / 2 : ℝ) ^ M - (1 / 2 : ℝ) ^ (M + 1)) := by
              rw [pow_add, pow_succ]; ring
            have hm' := hm.trans he.le
            set Y := 2 * c * (1 / 2 : ℝ) ^ X
            have hring : (X : ℝ) + Y * (1 - (1 / 2 : ℝ) ^ M) +
                Y * ((1 / 2 : ℝ) ^ M - (1 / 2 : ℝ) ^ (M + 1)) =
                X + Y * (1 - (1 / 2 : ℝ) ^ (M + 1)) := by ring
            linarith
        have := hb (N + 1 - X)
        rwa [show X + (N + 1 - X) = N + 1 by omega] at this
      rw [← sum_range_succ]
      have : 0 ≤ 2 * c * (1 / 2 : ℝ) ^ X * (1 / 2 : ℝ) ^ (N + 1 - X) := by positivity
      nlinarith

/-- Layer cake for the largest captured residual. -/
theorem bitsExpectation_capturedMax_le (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hqhalf : ∀ e, q e ≤ 1 / 2)
    (V : Finset α) (F : Finset (Finset α)) (hF : ∀ R ∈ F, R ⊆ V) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hcard : (F.card : ℝ) ≤ Real.exp (Λ * V.card)) :
    bitsExpectation q V (fun S => (capturedMax F S : ℝ)) ≤ Λ * V.card / Real.log 2 + 3 := by
  classical
  have hq1 : ∀ e, q e ≤ 1 := fun e => (hqhalf e).trans (by norm_num)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hstep (x : ℕ) : bitsExpectation q V (fun S => residualBadIndicator F x S) ≤
      min 1 ((F.card : ℝ) * (1 / 2 : ℝ) ^ x) := by
    apply le_min
    · calc _ ≤ bitsExpectation q V (fun _ => (1 : ℝ)) :=
            bitsExpectation_mono q hq0 hq1 V (fun S _ => residualBadIndicator_le_one F _ S)
        _ = 1 := bitsExpectation_const q V 1
    · have h := bitsExpectation_residualBad_le q hq0 hqhalf V F hF x
      have heq : Real.exp (-(x : ℝ) * Real.log 2) = (1 / 2 : ℝ) ^ x := by
        rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num)]; simp
      rwa [heq] at h
  set X := ⌈Λ * V.card / Real.log 2⌉₊
  have hX : (X : ℝ) ≤ Λ * V.card / Real.log 2 + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  have hFX : (F.card : ℝ) * (1 / 2 : ℝ) ^ X ≤ 1 := by
    have h2 : (1 / 2 : ℝ) ^ X = Real.exp (-(X : ℝ) * Real.log 2) := by
      rw [neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num)]; simp
    rw [h2]
    calc (F.card : ℝ) * Real.exp (-(X : ℝ) * Real.log 2)
        ≤ Real.exp (Λ * V.card) * Real.exp (-(X : ℝ) * Real.log 2) :=
          mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
      _ = Real.exp (Λ * V.card - X * Real.log 2) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp 0 := by
          apply Real.exp_le_exp.mpr
          have hc := Nat.le_ceil (Λ * V.card / Real.log 2)
          rw [div_le_iff₀ hlog] at hc
          linarith
      _ = 1 := Real.exp_zero
  calc bitsExpectation q V (fun S => (capturedMax F S : ℝ))
      ≤ bitsExpectation q V (fun S => ∑ x ∈ range V.card, residualBadIndicator F x S) :=
        bitsExpectation_mono q hq0 hq1 V (fun S _ => capturedMax_le_sum F V S hF)
    _ = ∑ x ∈ range V.card, bitsExpectation q V (fun S => residualBadIndicator F x S) :=
        bitsExpectation_sum q V _ _
    _ ≤ ∑ x ∈ range V.card, min 1 ((F.card : ℝ) * (1 / 2 : ℝ) ^ x) :=
        sum_le_sum (fun x _ => hstep x)
    _ ≤ X + 2 * (F.card : ℝ) * (1 / 2 : ℝ) ^ X :=
        sum_min_geometric _ (Nat.cast_nonneg _) X _
    _ ≤ Λ * V.card / Real.log 2 + 3 := by nlinarith

/-- The moment generating function of a Bernoulli sample size. -/
lemma bitsExpectation_pow_card (p r : ℝ) (V : Finset α) :
    bitsExpectation (fun _ => p) V (fun A => r ^ A.card) = (1 - p + p * r) ^ V.card := by
  induction V using Finset.induction_on with
  | empty => simp
  | @insert e V he ih =>
    rw [bitsExpectation_insert _ V e he]
    have hcong : bitsExpectation (fun _ => p) V (fun S => r ^ (insert e S).card) =
        r * bitsExpectation (fun _ => p) V (fun A => r ^ A.card) := by
      rw [← bitsExpectation_mul_const]
      apply bitsExpectation_congr
      intro S hS
      have heS : e ∉ S := fun h => he (hS h)
      rw [Finset.card_insert_of_notMem heS, pow_succ]; ring
    rw [hcong, ih, Finset.card_insert_of_notMem he, pow_succ]
    ring

/-- Chernoff bound by Markov's inequality on `r^|A|`. -/
theorem bitsExpectation_card_gt_le (p r : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : 1 ≤ r)
    (V : Finset α) (m : ℕ) :
    bitsExpectation (fun _ => p) V (fun A => if m < A.card then (1 : ℝ) else 0) ≤
      (1 - p + p * r) ^ V.card / r ^ (m + 1) := by
  have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
  have hpt (A : Finset α) : (if m < A.card then (1 : ℝ) else 0) ≤ r ^ A.card / r ^ (m + 1) := by
    split_ifs with h
    · rw [le_div_iff₀ (pow_pos hr0 _), one_mul]
      exact pow_le_pow_right₀ hr h
    · positivity
  calc _ ≤ bitsExpectation (fun _ => p) V (fun A => r ^ A.card / r ^ (m + 1)) :=
        bitsExpectation_mono _ (fun _ => hp0) (fun _ => hp1) V (fun A _ => hpt A)
    _ = (1 - p + p * r) ^ V.card / r ^ (m + 1) := by
        simp_rw [div_eq_inv_mul]
        rw [bitsExpectation_mul_const, bitsExpectation_pow_card]

end MatroidProphet

end OAI
