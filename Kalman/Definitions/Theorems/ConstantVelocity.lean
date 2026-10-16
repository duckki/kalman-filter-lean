import Kalman.Definitions.Theorems.JosephPositionCorrection

/-! Project specialization of linear prediction to position and velocity. -/

namespace Kalman.Definitions.Theorems.ConstantVelocity

open Matrix Kalman.Definitions.LinearModel

noncomputable section

/-- Constant velocity over a time increment `dt`, in position/velocity order. -/
def transition (dt : ℝ) : Square 2 := !![1, dt; 0, 1]

end
end Kalman.Definitions.Theorems.ConstantVelocity
