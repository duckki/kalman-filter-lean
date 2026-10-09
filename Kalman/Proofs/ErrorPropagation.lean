import Kalman.Implementation.Correctness.InputInterpretation
import Kalman.Proofs.ArithmeticProfiles
import Flare.Analysis.EntrywiseError
import Flare.Analysis.ErrorRecurrence

/-! Filter proof compatibility names for FLARE's reusable matrix propagation,
positivity margins, and scalar error recurrences. The authoritative statements
and proofs live in FLARE; this module contains no duplicate proof scripts. -/

namespace Kalman.Proofs.ErrorPropagation

alias within_trans := Flare.Analysis.EntrywiseError.within_trans
alias within_transpose := Flare.Analysis.EntrywiseError.within_transpose
alias within_add := Flare.Analysis.EntrywiseError.within_add
alias within_sub := Flare.Analysis.EntrywiseError.within_sub
alias within_refl := Flare.Analysis.EntrywiseError.within_refl
alias within_sym := Flare.Analysis.EntrywiseError.within_sym
alias within_mul := Flare.Analysis.EntrywiseError.within_mul
alias product_magnitude := Flare.Analysis.EntrywiseError.product_magnitude
alias within_mul_right := Flare.Analysis.EntrywiseError.within_mul_right
alias within_diagonal_mul_right := Flare.Analysis.EntrywiseError.within_diagonal_mul_right
alias within_mul_left := Flare.Analysis.EntrywiseError.within_mul_left
alias lower_bound_of_error := Flare.Analysis.EntrywiseError.lower_bound_of_error
alias posDef_of_error_margin := Flare.Analysis.EntrywiseError.posDef_of_error_margin
alias finite_horizon_bound := Flare.Analysis.ErrorRecurrence.finite_horizon_bound
alias nonexpansive_budget := Flare.Analysis.ErrorRecurrence.nonexpansive_budget

end Kalman.Proofs.ErrorPropagation
