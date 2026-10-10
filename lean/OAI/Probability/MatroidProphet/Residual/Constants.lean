import OAI.Probability.MatroidProphet.Constants
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

namespace MatroidProphet

/-- Residual size threshold `δ`. -/
noncomputable def residualDelta : ℝ := 1 / 16

theorem residual_error_constant :
    densityRate / (2 * densityThreshold) + residualError ≤ transferError := by
  norm_num [densityRate, densityThreshold, ruleKappa, residualError, transferError]

end MatroidProphet

end OAI
