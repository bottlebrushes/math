import OAI.Probability.MatroidProphet.Main

namespace OAI

/-!
# The source sacrificed-mask law for the secretary transport

The identities below concern the actual complete source seed.  They average
over the branch coin and all mask coordinates, including unused coordinates.
They do not assert a product law conditional on the complete secretary seed.
-/

namespace MatroidProphet

open MeasureTheory Finset

/-- Bernoulli rate of the main-branch sacrificed mask `H ∪ D ∪ C`. -/
noncomputable def secretaryMainRate : ℝ :=
  filterRate + (1 - filterRate) * (densityRate + (1 - densityRate) * thinningRate)

lemma secretary_main_rate_pos : 0 < secretaryMainRate := by
  norm_num [secretaryMainRate, filterRate, densityRate, thinningRate]

lemma secretary_main_rate_lt_one : secretaryMainRate < 1 := by
  norm_num [secretaryMainRate, filterRate, densityRate, thinningRate]

/-- The union of the three sacrificed main-branch masks has the Bernoulli rate
`secretaryMainRate`.  The test mask is not sacrificed. -/
theorem main_sacrificed_mask_expectation {α : Type*} [DecidableEq α]
    (V : Finset α) (f : Finset α → ℝ) :
    bitsExpectation (fun _ => filterRate) V (fun H =>
      bitsExpectation (fun _ => densityRate) V (fun D =>
        bitsExpectation (fun _ => thinningRate) V (fun C => f (H ∪ D ∪ C)))) =
      bitsExpectation (fun _ => secretaryMainRate) V f := by
  have hinner (H : Finset α) := bitsExpectation_union
    (fun _ : α => densityRate) (fun _ => thinningRate) V (fun S => f (H ∪ S))
  simp only [← Finset.union_assoc] at hinner
  simp_rw [hinner]
  rw [bitsExpectation_union]
  rfl

/-- The sacrificed mask of the implemented hidden rule, with its branch tag. -/
lemma completeHiddenRule_mask {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (r : Seed (mainSeedBits n)) :
    (completeHiddenRule M hE).mask r =
      if mainBranch r then (mainMasks r).H ∪ (mainMasks r).D ∪ (mainMasks r).C
      else (mainMasks r).H := by
  rfl

/-- Exact joint law of the branch and sacrificed mask.  Arbitrary real test
functions characterize the full finite joint law, not just its marginals. -/
theorem source_sacrificed_mask_expectation {n : ℕ} (M : Matroid (Fin n))
    (hE : M.E = Set.univ) (f : Bool → Finset (Fin n) → ℝ) :
    (∫ r, f (mainBranch r) ((completeHiddenRule M hE).mask r) ∂sourceSeedLaw n) =
      branchRate *
        bitsExpectation (fun _ => filterRate) Finset.univ (f false) +
      (1 - branchRate) *
        bitsExpectation (fun _ => secretaryMainRate) Finset.univ (f true) := by
  simp_rw [completeHiddenRule_mask]
  rw [integral_sourceSeedLaw (fun d b =>
    f b (if b then d.H ∪ d.D ∪ d.C else d.H))]
  simp only [branchExpectation, fairParityExpectation, add_self_div_two,
    Bool.false_eq_true, ↓reduceIte]
  simp only [bitsExpectation_add, bitsExpectation_mul_const, bitsExpectation_const]
  rw [main_sacrificed_mask_expectation]
  ring

end MatroidProphet

end OAI
