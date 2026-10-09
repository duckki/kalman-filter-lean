import Kalman.Definitions.OrthogonalFactorization

/-! Exact Gram preservation for the normalized reflection reference.
The authoritative coordinate bound and reflection proof are in FLARE. -/

namespace Kalman.Proofs.OrthogonalStructure

alias unit_component_bound := Flare.Analysis.Householder.unit_component_bound
alias reflect_gram := Flare.Analysis.Householder.reflect_gram

end Kalman.Proofs.OrthogonalStructure
