import OAI.Probability.MatroidProphet.Constants
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

namespace MatroidProphet

/-- Residual size threshold `δ`. -/
noncomputable def residualDelta : ℝ := 1 / 50

theorem residual_error_constant :
    densityThreshold⁻¹ + residualDelta + residualTail ≤ transferError := by
  norm_num [densityThreshold, residualDelta, residualTail, transferError]

end MatroidProphet

end OAI
