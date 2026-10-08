import OAI.Probability.MatroidProphet.Reverse.LowHazard
import OAI.Probability.MatroidProphet.Reverse.ExitDual

namespace OAI

namespace MatroidProphet
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

noncomputable def exitHazardCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (k : ℤ) (S _ : ℕ → Set α) : ℝ :=
  if d ∈ S h then reverseHazard M hE κ D G q d h k S else 0

noncomputable def squareHazardCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (k : ℤ) (S _ : ℕ → Set α) : ℝ :=
  if d ∈ S h then (reverseHazard M hE κ D G q d h k S)^2 else 0

lemma exitHazardCost_mean_eq_exit (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (h : ℕ) (hh : h ≤ n) (m : ℕ) (k : ℤ) (S : ℕ → Set α)
    (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q (exitHazardCost M hE κ D G q d h) m k S =
      reverseMeanCost M hE κ D G n q (exitCost d h) m k S := by
  apply reverseMeanCost_eq_of_step M hE κ D G n hG q hq0 hq1
  · intro l R hR
    by_cases hd : d ∈ R h
    · simp only [exitHazardCost, hd, ite_true, bitsExpectation_const, exitCost, true_and]
      exact reverseHazard_eq_step M hE κ D G n hG q d h hh l R
    · simp only [exitHazardCost, hd, ite_false, bitsExpectation_const, exitCost, false_and]
  · exact closed

private lemma bitsExpectation_sub' (q : α → ℝ) (V : Finset α) (f g : Finset α → ℝ) :
    bitsExpectation q V (fun H => f H - g H) = bitsExpectation q V f - bitsExpectation q V g := by
  simp only [bitsExpectation, mul_sub, Finset.sum_sub_distrib]

/-- Survival weight `1 - h` of a live step whose hazard is at least `p₀`. -/
noncomputable def aliveThresholdCost (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (q : α → ℝ) (d : α) (h : ℕ)
    (p₀ : ℝ) (k : ℤ) (S _ : ℕ → Set α) : ℝ :=
  if d ∈ S h ∧ p₀ ≤ reverseHazard M hE κ D G q d h k S then
    1 - reverseHazard M hE κ D G q d h k S else 0

lemma aliveThresholdCost_mean_eq (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (d : α) (h : ℕ) (hh : h ≤ n)
    (p₀ : ℝ) (m : ℕ) (k : ℤ) (S : ℕ → Set α) (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q (aliveThresholdCost M hE κ D G q d h p₀) m k S =
      reverseMeanCost M hE κ D G n q (bandNonexitCost M hE κ D G q d h p₀ 2) m k S := by
  apply reverseMeanCost_eq_of_step M hE κ D G n hG q hq0 hq1
  · intro l R hR
    have hz1 := reverseHazard_le_one M hE κ D G q hq0 hq1 d h l R
    have hlt : reverseHazard M hE κ D G q d h l R < 2 := by linarith
    simp only [aliveThresholdCost]
    rw [bitsExpectation_const]
    by_cases hd : d ∈ R h
    · by_cases hp : p₀ ≤ reverseHazard M hE κ D G q d h l R
      · have hstep := reverseHazard_eq_step M hE κ D G n hG q d h hh l R
        have hsplit : bitsExpectation q univ (fun C =>
            bandNonexitCost M hE κ D G q d h p₀ 2 l R ((reverseStepTree M hE κ l D R G n).run C)) =
            bitsExpectation q univ (fun C => 1 - (if d ∉ (reverseStepTree M hE κ l D R G n).run C h
              then (1:ℝ) else 0)) := by
          apply bitsExpectation_congr
          intro C hC
          by_cases hs : d ∈ (reverseStepTree M hE κ l D R G n).run C h <;>
            simp [bandNonexitCost, hp, hlt, hs]
        rw [hsplit, bitsExpectation_sub', bitsExpectation_const, ← hstep]
        simp [aliveThresholdCost, hd, hp]
      · simp [bandNonexitCost, hp, bitsExpectation_const]
    · have hz : ∀ C, bandNonexitCost M hE κ D G q d h p₀ 2 l R
          ((reverseStepTree M hE κ l D R G n).run C) = 0 := by
        intro C
        have hc := reverseStepTree_contracts M hE κ l D R G n hR C h
        unfold bandNonexitCost
        apply ite_eq_right
        intro hb
        exact hd (hc hb.2.2)
      simp [hd, hz, bitsExpectation_const]
  · exact closed

lemma aliveThresholdCost_mean_le (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1) (d : α) (h : ℕ) (hh : h ≤ n)
    (p₀ : ℝ) (hp : 0 < p₀) (hp1 : p₀ ≤ 1) (m : ℕ) (k : ℤ) (S : ℕ → Set α)
    (closed : ReverseClosed M hE κ D k S) :
    reverseMeanCost M hE κ D G n q (aliveThresholdCost M hE κ D G q d h p₀) m k S ≤
      Real.log (1 / p₀) := by
  rw [aliveThresholdCost_mean_eq M hE κ D G n hG q hq0 hq1 d h hh p₀ m k S closed]
  exact bandNonexitCost_budget M hE κ D G n hG q hq0 hq1 d h p₀ 2 hp hp1 m k S closed

/-- Squared exit mass (sharpened form of paper Lemma 4.2), by duality: the expected number of
non-exit steps with hazard at least `p` is at most `log (1/p)` and the exit mass is one. -/
theorem reverse_squared_exit_mass (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α) (n : ℕ)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (d : α) (hd : d ∉ M.closure ∅) (h : ℕ) (hh : h ≤ n) :
    exitMass ≤
      reverseMeanCost M hE κ D G n q (squareHazardCost M hE κ D G q d h)
        (pathHorizon h+1) (-1) (fun _ => Set.univ) := by
  set m := pathHorizon h + 1
  set S0 : ℕ → Set α := fun _ => Set.univ
  have closed := reverseClosed_univ M hE κ D (-1)
  let η : ℝ := ((2:ℝ)^12)⁻¹
  let A : ℕ → ℤ → (ℕ → Set α) → (ℕ → Set α) → ℝ := fun i =>
    aliveThresholdCost M hE κ D G q d h (exitThresholdAt i)
  have hpoint (k : ℤ) (S S' : ℕ → Set α) :
      (1/2 : ℝ) * exitHazardCost M hE κ D G q d h k S S' ≤
        squareHazardCost M hE κ D G q d h k S S' +
          ∑ i ∈ range 11, exitWeight i * A i k S S' +
            (1/2 : ℝ) * lowHazardCost M hE κ D G q d h η k S S' := by
    by_cases hs : d ∈ S h
    · set x := reverseHazard M hE κ D G q d h k S with hx
      have hx0 : 0 ≤ x := reverseHazard_nonneg M hE κ D G q hq0 hq1 d h k S
      have hx1 : x ≤ 1 := reverseHazard_le_one M hE κ D G q hq0 hq1 d h k S
      have key := exit_pointwise x hx0 hx1
      have hA : ∑ i ∈ range 11, exitWeight i * A i k S S' =
          (1 - x) * exitCertificate x := by
        unfold exitCertificate
        rw [mul_sum]
        apply sum_congr rfl
        intro i hi
        simp only [A, aliveThresholdCost, hs, true_and, ← hx]
        split_ifs <;> ring
      have hL : lowHazardCost M hE κ D G q d h η k S S' =
          (if x < ((2 : ℝ) ^ 12)⁻¹ then x else 0) := by
        simp only [lowHazardCost, hs, true_and, ← hx, η]
      simp only [exitHazardCost, squareHazardCost, hs, ite_true, ← hx]
      rw [hA, hL]
      linarith
    · simp [exitHazardCost, squareHazardCost, lowHazardCost, A, aliveThresholdCost, hs]
  have hmean :
      (1/2 : ℝ) * reverseMeanCost M hE κ D G n q (exitHazardCost M hE κ D G q d h) m (-1) S0 ≤
        reverseMeanCost M hE κ D G n q (squareHazardCost M hE κ D G q d h) m (-1) S0 +
          ∑ i ∈ range 11, exitWeight i * reverseMeanCost M hE κ D G n q (A i) m (-1) S0 +
            (1/2 : ℝ) * reverseMeanCost M hE κ D G n q
              (lowHazardCost M hE κ D G q d h η) m (-1) S0 := by
    rw [← reverseMeanCost_mul, ← reverseMeanCost_mul]
    simp_rw [← reverseMeanCost_mul]
    rw [← reverseMeanCost_sum, ← reverseMeanCost_add, ← reverseMeanCost_add]
    unfold reverseMeanCost
    apply bitsExpectation_mono q hq0 hq1
    intro C hC
    exact reverseCost_mono M hE κ D G n _ _ hpoint _ _ _ C
  rw [exitHazardCost_mean_eq_exit M hE κ D G n hG q hq0 hq1 d h hh _ _ _ closed,
    reverse_exit_total_one M hE κ D G n hG q d hd h hh, mul_one] at hmean
  have hA (i : ℕ) (hi : i ∈ range 11) :
      exitWeight i * reverseMeanCost M hE κ D G n q (A i) m (-1) S0 ≤
        exitWeight i * (((i : ℝ) + 2) * Real.log 2) := by
    apply mul_le_mul_of_nonneg_left _ (exitWeight_nonneg i (mem_range.mp hi))
    have hp : 0 < exitThresholdAt i := by unfold exitThresholdAt; positivity
    have hp1 : exitThresholdAt i ≤ 1 := by
      unfold exitThresholdAt
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    have hb := aliveThresholdCost_mean_le M hE κ D G n hG q hq0 hq1 d h hh _ hp hp1 m (-1) S0 closed
    have hlog : Real.log (1 / exitThresholdAt i) = ((i : ℝ) + 2) * Real.log 2 := by
      unfold exitThresholdAt
      rw [one_div, inv_inv, Real.log_pow]
      push_cast
      ring
    rw [hlog] at hb
    exact hb
  have hsum := sum_le_sum hA
  have hlow := reverse_low_hazard_le_potential M hE κ D G n hG q hq0 hq1 d h hh m (-1) S0 closed
  have hval := exit_dual_value
  have hlow' : (1/2 : ℝ) * reverseMeanCost M hE κ D G n q
      (lowHazardCost M hE κ D G q d h η) m (-1) S0 ≤ 1/2 * hazardTailPotential 12 := by
    apply mul_le_mul_of_nonneg_left hlow (by norm_num)
  linarith

end MatroidProphet

end OAI
