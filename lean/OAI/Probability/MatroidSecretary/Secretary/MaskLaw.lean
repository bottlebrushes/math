import OAI.Probability.MatroidSecretary.Secretary.MaskModel
import OAI.Probability.MatroidProphet.Main

namespace OAI

/-! Exact branch/sacrificed-mask marginal of the complete source law.

This marginal is taken after integrating all source coins, including test,
parity and unused coins. It is not a product-law assertion conditional on the
entire secretary seed.

Pinned source: `sections/secretary.tex`, lines 41--52 and 68--78,
SHA256 `3554fe0f7296782edf63cc7f1305c377e7a7b9d8f8948b9510ea4ad02a702d63`.
These are supporting obligations of `cor:secretary`, not the complete endpoint.
-/

namespace MatroidProphet.Secretary

open MeasureTheory Finset

lemma sacrificeRate_pos (j : Bool) : 0 < sacrificeRate j := by
  cases j <;> norm_num [sacrificeRate, filterRate, densityRate, thinningRate]

lemma sacrificeRate_lt_one (j : Bool) : sacrificeRate j < 1 := by
  cases j <;> norm_num [sacrificeRate, filterRate, densityRate, thinningRate]

lemma sacrificeRate_main :
    sacrificeRate true =
      filterRate + (1 - filterRate) * (densityRate + (1 - densityRate) * thinningRate) := by
  simp [sacrificeRate]

lemma sourceMask_eq_completeHiddenRule {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (r : Seed (mainSeedBits n)) :
    sourceMask r = (completeHiddenRule M hE).mask r := by
  rfl

lemma triple_mask_expectation {n : ℕ} (f : Finset (Fin n) → ℝ) :
    bitsExpectation (fun _ : Fin n => filterRate) univ (fun H =>
      bitsExpectation (fun _ : Fin n => densityRate) univ (fun D =>
        bitsExpectation (fun _ : Fin n => thinningRate) univ (fun C => f (H ∪ D ∪ C)))) =
      bitsExpectation (fun _ : Fin n => sacrificeRate true) univ f := by
  have hDC (H : Finset (Fin n)) :
      bitsExpectation (fun _ : Fin n => densityRate) univ (fun D =>
        bitsExpectation (fun _ : Fin n => thinningRate) univ (fun C => f (H ∪ D ∪ C))) =
      bitsExpectation (fun _ : Fin n => densityRate + (1 - densityRate) * thinningRate) univ
        (fun S => f (H ∪ S)) := by
    simpa only [Finset.union_assoc] using
      bitsExpectation_union (fun _ : Fin n => densityRate)
        (fun _ : Fin n => thinningRate) univ (fun S => f (H ∪ S))
  simp_rw [hDC]
  rw [bitsExpectation_union]
  simp only [sacrificeRate_main]

/-- Joint branch/mask law. All unused source coins are integrated, not discarded
from the information available to the adversary. -/
theorem integral_branch_sourceMask {n : ℕ} (j : Bool) (f : Finset (Fin n) → ℝ) :
    (∫ r, (if mainBranch r = j then f (sourceMask r) else 0) ∂sourceSeedLaw n) =
      branchWeight j * bitsExpectation (fun _ : Fin n => sacrificeRate j) univ f := by
  have h := integral_sourceSeedLaw (fun d b =>
    if b = j then f (if b then d.H ∪ d.D ∪ d.C else d.H) else 0)
  change (∫ r, (if mainBranch r = j then
    f (if mainBranch r then (mainMasks r).H ∪ (mainMasks r).D ∪ (mainMasks r).C
      else (mainMasks r).H) else 0) ∂sourceSeedLaw n) = _
  rw [h]
  cases j
  · simp only [branchExpectation, fairParityExpectation, Bool.false_eq_true, Bool.true_eq_false,
      ↓reduceIte, mul_zero, zero_add, add_self_div_two]
    simp only [bitsExpectation_const, bitsExpectation_mul_const]
    simp only [sacrificeRate, branchWeight, Bool.false_eq_true, ↓reduceIte]
  · simp only [branchExpectation, fairParityExpectation, Bool.false_eq_true, ↓reduceIte,
      mul_zero, add_zero, add_self_div_two]
    simp only [bitsExpectation_const, bitsExpectation_mul_const]
    rw [triple_mask_expectation f]
    simp only [branchWeight, ↓reduceIte]

/-- Every branch/mask fiber has its explicit positive Bernoulli product mass. -/
lemma integral_sourceMask_atom {n : ℕ} (j : Bool) (P : Finset (Fin n)) :
    (∫ r, (if mainBranch r = j ∧ sourceMask r = P then (1 : ℝ) else 0)
      ∂sourceSeedLaw n) =
      branchWeight j * bitsWeight (fun _ : Fin n => sacrificeRate j) univ P := by
  classical
  simpa [bitsExpectation, ite_and] using
    integral_branch_sourceMask j (fun S => if S = P then (1 : ℝ) else 0)

lemma bitsWeight_sacrificeRate_pos {n : ℕ} (j : Bool) (P : Finset (Fin n)) :
    0 < bitsWeight (fun _ : Fin n => sacrificeRate j) univ P := by
  unfold bitsWeight
  apply Finset.prod_pos
  intro e he
  split_ifs
  · exact sacrificeRate_pos j
  · exact sub_pos.mpr (sacrificeRate_lt_one j)

lemma sourceMask_atom_real {n : ℕ} (j : Bool) (P : Finset (Fin n)) :
    (sourceSeedLaw n).real {r | mainBranch r = j ∧ sourceMask r = P} =
      branchWeight j * bitsWeight (fun _ : Fin n => sacrificeRate j) univ P := by
  classical
  rw [← integral_indicator_one (Set.to_countable _).measurableSet]
  simpa only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply] using
    integral_sourceMask_atom j P

lemma sourceMask_atom {n : ℕ} (j : Bool) (P : Finset (Fin n)) :
    sourceSeedLaw n {r | mainBranch r = j ∧ sourceMask r = P} =
      ENNReal.ofReal (branchWeight j * bitsWeight (fun _ : Fin n => sacrificeRate j) univ P) := by
  rw [← sourceMask_atom_real, ofReal_measureReal]

lemma sourceMask_atom_pos {n : ℕ} (j : Bool) (P : Finset (Fin n)) :
    0 < sourceSeedLaw n {r | mainBranch r = j ∧ sourceMask r = P} := by
  rw [sourceMask_atom, ENNReal.ofReal_pos]
  exact mul_pos (branchWeight_pos j) (bitsWeight_sacrificeRate_pos j P)

/-- The same atom identity stated directly for the source algorithm's actual
branch-tagged observation; this is the finite conditional-kernel interface. -/
theorem completeHiddenRule_joint_atom {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (j : Bool) (P : Finset (Fin n)) :
    sourceSeedLaw n {r | (mainBranch r, (completeHiddenRule M hE).mask r) = (j, P)} =
      ENNReal.ofReal (branchWeight j * bitsWeight (fun _ : Fin n => sacrificeRate j) univ P) := by
  simpa only [Prod.mk.injEq, ← sourceMask_eq_completeHiddenRule M hE] using
    sourceMask_atom j P

theorem completeHiddenRule_joint_atom_pos {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (j : Bool) (P : Finset (Fin n)) :
    0 < sourceSeedLaw n {r | (mainBranch r, (completeHiddenRule M hE).mask r) = (j, P)} := by
  simpa only [Prod.mk.injEq, ← sourceMask_eq_completeHiddenRule M hE] using
    sourceMask_atom_pos j P

end MatroidProphet.Secretary

end OAI
