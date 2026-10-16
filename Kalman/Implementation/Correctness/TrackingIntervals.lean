import Kalman.Implementation.Correctness.UncertaintyIntervals
import Kalman.Implementation.Correctness.UniformTrackingAccuracy

namespace Kalman.Implementation.Correctness.TrackingIntervals

open Kalman.Definitions Kalman.Implementation.UncertaintyIntervals
  Kalman.Implementation.Correctness.InputInterpretation

noncomputable section

/-- Every certified stationary coupled prefix has actual executable interval
endpoints, with ideal statistical coverage remaining a caller premise.
Witness: `FloatTrackingIntervals.horizon_intervals`. -/
def HorizonIntervals : Prop :=
  ∀ (measurements : Nat → Float) (initial : Input.State) (horizon : Nat),
    ConstantVelocityTracking.HorizonDomain measurements initial horizon
    → ∀ t,
        t ≤ horizon
        → ∃ output,
            SymmetricJosephFilter.run
                (fun k => ConstantVelocityTracking.trackingInput (measurements k)) initial
                t
              = .ok output
            ∧ ∀ (i : Fin 2) (multiplier : Float),
                multiplier.isFinite = true
                → 0 ≤ Flare.Binary64.Value.value multiplier
                → Flare.Binary64.Value.value multiplier ≤ 8
                → UncertaintyIntervals.Enclosure (output.mean.getD i.val 0.0)
                    (output.covariance.getD (i.val * 2 + i.val) 0.0) 0.0
                    trackingMeanAllowance multiplier
                    ((exactRun 2 1
                        (fun k => ConstantVelocityTracking.trackingInput (measurements k))
                        (state 2 initial) t).mean
                      i)
                    ((exactRun 2 1
                        (fun k => ConstantVelocityTracking.trackingInput (measurements k))
                        (state 2 initial) t).covariance
                      i i)

end
end Kalman.Implementation.Correctness.TrackingIntervals
