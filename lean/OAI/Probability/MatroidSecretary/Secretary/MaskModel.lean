import OAI.Probability.MatroidProphet.Main

namespace OAI

/-! Concrete sacrificed-mask data for the secretary transport.

The branch and every mask coordinate are functions of the complete source seed.
The test mask is deliberately not part of the sacrificed mask.
-/

namespace MatroidProphet.Secretary

/-- The observation mask of the concrete source rule, before any values are seen. -/
noncomputable def sourceMask {n : ℕ} (r : Seed (mainSeedBits n)) : Finset (Fin n) :=
  if mainBranch r then
    (mainMasks r).H ∪ (mainMasks r).D ∪ (mainMasks r).C
  else (mainMasks r).H

/-- Branchwise Bernoulli rates of the sacrificed mask (`sections/secretary.tex`, with the
sharpened mask rates). `false` is the maximum branch and `true` is the main branch. -/
noncomputable def sacrificeRate (j : Bool) : ℝ :=
  if j then filterRate + (1 - filterRate) * (densityRate + (1 - densityRate) * thinningRate)
  else filterRate

/-- Probability of each branch: the maximum branch has probability `branchRate`. -/
noncomputable def branchWeight (j : Bool) : ℝ :=
  if j then 1 - branchRate else branchRate

lemma branchWeight_pos (j : Bool) : 0 < branchWeight j := by
  cases j <;> norm_num [branchWeight, branchRate]

end MatroidProphet.Secretary

end OAI
