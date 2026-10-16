import Kalman.Definitions.Input

/-! Stored position/velocity model constructor. Parameters and measurements
are copied without arithmetic; the checked filter performs input validation. -/

namespace Kalman.Implementation.PositionVelocityModel

open Kalman.Definitions.Input

/-- Original stored time increment and independent process/measurement variances. -/
structure Parameters where
  timeStep : Float
  positionProcessVariance : Float
  velocityProcessVariance : Float
  measurementVariance : Float
deriving Repr

/-- Position observation of a constant-velocity state with diagonal process
noise. This storage constructor does not calibrate or validate parameters. -/
def input (p : Parameters) (measurement : Float) : Model :=
  ⟨
    2,
    1,
    #[1.0, p.timeStep, 0.0, 1.0],
    #[1.0, 0.0],
    #[p.positionProcessVariance, 0.0, 0.0, p.velocityProcessVariance],
    #[p.measurementVariance],
    #[measurement]
  ⟩

end Kalman.Implementation.PositionVelocityModel
