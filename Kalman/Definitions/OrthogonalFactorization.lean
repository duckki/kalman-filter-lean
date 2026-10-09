import Flare.Analysis.Householder

/-! Exact normalized Householder action used to interpret the native QR stages.
This is the project algebraic reference H A, H = I - 2 u uᵀ, for a unit vector u;
it does not choose the ideal QR reflector of the original input. -/

namespace Kalman.Definitions.OrthogonalFactorization

noncomputable section

abbrev reflect {height width : Nat} (u : Fin height → ℝ)
    (a : Matrix (Fin height) (Fin width) ℝ)
    : Matrix (Fin height) (Fin width) ℝ :=
  Flare.Analysis.Householder.reflect u a

end
end Kalman.Definitions.OrthogonalFactorization
