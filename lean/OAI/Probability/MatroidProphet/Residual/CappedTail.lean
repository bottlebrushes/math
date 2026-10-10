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

/-- Geometric tail sum with ratio `ρ`. -/
lemma sum_min_geometric (ρ c : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hc : 0 ≤ c) (X N : ℕ) :
    (∑ x ∈ range N, min 1 (c * ρ ^ x)) ≤ X + c * ρ ^ X / (1 - ρ) := by
  have h1ρ : 0 < 1 - ρ := by linarith
  have hY0 : 0 ≤ c * ρ ^ X / (1 - ρ) := by positivity
  have hfirst : ∀ M ≤ X, (∑ x ∈ range M, min 1 (c * ρ ^ x)) ≤ M := by
    intro M _
    calc (∑ x ∈ range M, min 1 (c * ρ ^ x)) ≤ ∑ x ∈ range M, (1 : ℝ) :=
          sum_le_sum (fun x _ => min_le_left _ _)
      _ = M := by simp
  have hb : ∀ M : ℕ, (∑ x ∈ range (X + M), min 1 (c * ρ ^ x)) ≤
      X + c * ρ ^ X / (1 - ρ) * (1 - ρ ^ M) := by
    intro M
    induction M with
    | zero => simpa using hfirst X le_rfl
    | succ M ihM =>
      rw [← add_assoc, sum_range_succ]
      have hm : min 1 (c * ρ ^ (X + M)) ≤ c * ρ ^ (X + M) := min_le_right _ _
      have he : c * ρ ^ (X + M) = c * ρ ^ X / (1 - ρ) * (ρ ^ M - ρ ^ (M + 1)) := by
        field_simp
        rw [pow_add, pow_succ]; ring
      have hring : (X : ℝ) + c * ρ ^ X / (1 - ρ) * (1 - ρ ^ M) +
          c * ρ ^ X / (1 - ρ) * (ρ ^ M - ρ ^ (M + 1)) =
          X + c * ρ ^ X / (1 - ρ) * (1 - ρ ^ (M + 1)) := by ring
      linarith [hm.trans he.le]
  by_cases hN : N ≤ X
  · have := hfirst N hN
    have hX : (N : ℝ) ≤ X := by exact_mod_cast hN
    linarith
  · have h := hb (N - X)
    rw [show X + (N - X) = N by omega] at h
    have hp : 0 ≤ c * ρ ^ X / (1 - ρ) * ρ ^ (N - X) := by positivity
    nlinarith

/-- Layer cake for the largest captured residual at mask rate at most `ρ`. -/
theorem bitsExpectation_capturedMax_le (q : α → ℝ) (ρ : ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hqρ : ∀ e, q e ≤ ρ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (V : Finset α) (F : Finset (Finset α)) (hF : ∀ R ∈ F, R ⊆ V) (Λ : ℝ) (hΛ : 0 ≤ Λ)
    (hcard : (F.card : ℝ) ≤ Real.exp (Λ * V.card)) :
    bitsExpectation q V (fun S => (capturedMax F S : ℝ)) ≤
      Λ * V.card / Real.log (1 / ρ) + 1 / (1 - ρ) := by
  classical
  have hq1 : ∀ e, q e ≤ 1 := fun e => (hqρ e).trans hρ1.le
  have hlog : 0 < Real.log (1 / ρ) := Real.log_pos (by rw [lt_div_iff₀ hρ0]; linarith)
  have hstep (x : ℕ) : bitsExpectation q V (fun S => residualBadIndicator F x S) ≤
      min 1 (((F.card : ℝ) * ρ) * ρ ^ x) := by
    apply le_min
    · calc _ ≤ bitsExpectation q V (fun _ => (1 : ℝ)) :=
            bitsExpectation_mono q hq0 hq1 V (fun S _ => residualBadIndicator_le_one F _ S)
        _ = 1 := bitsExpectation_const q V 1
    · calc _ ≤ bitsExpectation q V (fun S => ∑ R ∈ F,
            if (x : ℝ) < (R.card : ℝ) then (if R ⊆ S then (1 : ℝ) else 0) else 0) :=
            bitsExpectation_mono q hq0 hq1 V (fun S _ => residualBad_indicator_le F x S)
        _ = ∑ R ∈ F, bitsExpectation q V (fun S =>
            if (x : ℝ) < (R.card : ℝ) then (if R ⊆ S then (1 : ℝ) else 0) else 0) :=
            bitsExpectation_sum q V F _
        _ ≤ ∑ _R ∈ F, ρ ^ (x + 1) := by
            apply sum_le_sum
            intro R hRF
            by_cases hRt : (x : ℝ) < (R.card : ℝ)
            · simp only [hRt, ite_true]
              rw [bitsExpectation_contains q V R (hF R hRF)]
              have hxR : x + 1 ≤ R.card := by exact_mod_cast hRt
              calc ∏ e ∈ R, q e ≤ ∏ _e ∈ R, ρ :=
                    Finset.prod_le_prod₀ (fun e _ => hq0 e) (fun e _ => hqρ e)
                _ = ρ ^ R.card := by simp
                _ ≤ ρ ^ (x + 1) := pow_le_pow_of_le_one hρ0.le hρ1.le hxR
            · simp only [hRt, ite_false, bitsExpectation_const]
              positivity
        _ = ((F.card : ℝ) * ρ) * ρ ^ x := by rw [sum_const, nsmul_eq_mul, pow_succ]; ring
  set X := ⌊Λ * V.card / Real.log (1 / ρ)⌋₊
  have hX : (X : ℝ) ≤ Λ * V.card / Real.log (1 / ρ) := Nat.floor_le (by positivity)
  have hFX : (F.card : ℝ) * ρ * ρ ^ X ≤ 1 := by
    have hlt := Nat.lt_floor_add_one (Λ * V.card / Real.log (1 / ρ))
    rw [div_lt_iff₀ hlog] at hlt
    have hpow : ρ ^ (X + 1) = Real.exp (-((X : ℝ) + 1) * Real.log (1 / ρ)) := by
      rw [neg_mul, Real.exp_neg, ← Real.exp_log (pow_pos hρ0 (X + 1)), Real.log_pow,
        one_div, Real.log_inv, ← Real.exp_neg]
      push_cast; ring_nf
    calc (F.card : ℝ) * ρ * ρ ^ X = (F.card : ℝ) * ρ ^ (X + 1) := by ring
      _ ≤ Real.exp (Λ * V.card) * Real.exp (-((X : ℝ) + 1) * Real.log (1 / ρ)) := by
          rw [hpow]; exact mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
      _ = Real.exp (Λ * V.card - ((X : ℝ) + 1) * Real.log (1 / ρ)) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have h1ρ : 0 < 1 - ρ := by linarith
  calc bitsExpectation q V (fun S => (capturedMax F S : ℝ))
      ≤ bitsExpectation q V (fun S => ∑ x ∈ range V.card, residualBadIndicator F x S) :=
        bitsExpectation_mono q hq0 hq1 V (fun S _ => capturedMax_le_sum F V S hF)
    _ = ∑ x ∈ range V.card, bitsExpectation q V (fun S => residualBadIndicator F x S) :=
        bitsExpectation_sum q V _ _
    _ ≤ ∑ x ∈ range V.card, min 1 (((F.card : ℝ) * ρ) * ρ ^ x) :=
        sum_le_sum (fun x _ => hstep x)
    _ ≤ X + (F.card : ℝ) * ρ * ρ ^ X / (1 - ρ) :=
        sum_min_geometric ρ _ hρ0.le hρ1 (by positivity) X _
    _ ≤ Λ * V.card / Real.log (1 / ρ) + 1 / (1 - ρ) := by
        have : (F.card : ℝ) * ρ * ρ ^ X / (1 - ρ) ≤ 1 / (1 - ρ) :=
          div_le_div_of_nonneg_right hFX h1ρ.le
        linarith

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
