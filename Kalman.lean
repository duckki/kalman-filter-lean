-- Source equations and decoded inputs.
import Kalman.Definitions.LinearModel
import Kalman.Definitions.CovarianceRecursion
import Kalman.Definitions.FactorRecursion
import Kalman.Definitions.OrthogonalFactorization
import Kalman.Definitions.Input
import Kalman.Definitions.DiagonalObservation

-- Main exact Real result statements.
import Kalman.Definitions.Theorems.CovariancePositiveDefiniteness
import Kalman.Definitions.Theorems.FormulationEquivalence
import Kalman.Definitions.Theorems.RecursionSensitivity

-- Executable native Float algorithms.
import Kalman.Implementation.LinearAlgebra
import Kalman.Implementation.CovarianceFilter
import Kalman.Implementation.OrthogonalFactorization
import Kalman.Implementation.SquareRootFilter

-- Shared native interpretation.
import Kalman.Implementation.Correctness.InputInterpretation

-- Main native implementation guarantees.
import Kalman.Implementation.Correctness.CovarianceCounterexamples
import Kalman.Implementation.Correctness.JosephCovarianceEvaluation
import Kalman.Implementation.Correctness.FullyObservedDiagonalJosephAccuracy
import Kalman.Implementation.Correctness.SquareRootFilterProperties
import Kalman.Implementation.Correctness.CorrelatedNoiseFilterAccuracy
import Kalman.Implementation.Correctness.FullyObservedDiagonalFilterAccuracy

-- Proof witnesses.
import Kalman.Proofs.CovarianceStructure
import Kalman.Proofs.RealRecursion
import Kalman.Proofs.FactorStructure
import Kalman.Proofs.FloatCounterexamples
import Kalman.Proofs.FloatTraceCounterexample
import Kalman.Proofs.FloatDenseError
import Kalman.Proofs.FloatSolveError
import Kalman.Proofs.FloatFactorValidity
import Kalman.Proofs.FloatMaterialization
import Kalman.Proofs.FloatGramSymmetry
import Kalman.Proofs.ErrorPropagation
import Kalman.Proofs.FloatJosephError
import Kalman.Proofs.FloatJosephDomain
import Kalman.Proofs.FloatJosephSolve
import Kalman.Proofs.FloatJosephStructure
import Kalman.Proofs.FloatJosephGain
import Kalman.Proofs.FloatJosephUpdate
import Kalman.Proofs.FloatUnderflow
import Kalman.Proofs.FloatResidualError
import Kalman.Proofs.FloatCholeskySolve
import Kalman.Proofs.FloatCholeskyFactor
import Kalman.Proofs.FloatErrorBounds
import Kalman.Proofs.FloatQRNorm
import Kalman.Proofs.FloatQRReflector
import Kalman.Proofs.FloatQRApplication
import Kalman.Proofs.FloatQRFinish
import Kalman.Proofs.FloatQRIteration
import Kalman.Proofs.FloatQRRetain
import Kalman.Proofs.FloatQRTriangular
import Kalman.Proofs.OrthogonalStructure
import Kalman.Proofs.FloatQRGram
import Kalman.Proofs.FloatQRComposition
import Kalman.Proofs.FloatQRDomain
import Kalman.Proofs.FloatQRSourceTail
import Kalman.Proofs.FloatQRInitialDomain
import Kalman.Proofs.FloatPrearray
import Kalman.Proofs.FloatSquareRootError
import Kalman.Proofs.RealErrorBounds
import Kalman.Proofs.FloatSquareRootUpdate
import Kalman.Proofs.RecursionSensitivity
import Kalman.Proofs.FloatFullFilter
import Kalman.Proofs.FloatFilterInitialization
import Kalman.Proofs.FloatCholeskyDomain
import Kalman.Proofs.FloatCholeskySolveDomain
import Kalman.Proofs.FloatQRFactorDomain
import Kalman.Proofs.FloatGainDomain
import Kalman.Proofs.FloatInnovationDomain
import Kalman.Proofs.FloatMeanDomain
import Kalman.Proofs.FloatPredictionDomain
import Kalman.Proofs.PosteriorStructure
import Kalman.Proofs.FloatPosteriorPrearray
import Kalman.Proofs.FloatPosteriorDomain
import Kalman.Proofs.FloatFilterInputDomain
import Kalman.Proofs.RealFilterInvariant
import Kalman.Proofs.RealDiagonalObservation
import Kalman.Proofs.RealObservableInvariant
import Kalman.Proofs.RealObservableSensitivity
import Kalman.Proofs.FloatDiagonalStorage
import Kalman.Proofs.FloatQRDiagonal
import Kalman.Proofs.FloatObservablePrediction
import Kalman.Proofs.FloatObservableInnovation
import Kalman.Proofs.FloatObservableDiagonal
import Kalman.Proofs.FloatDiagonalSolve
import Kalman.Proofs.FloatObservableGain
import Kalman.Proofs.FloatObservableMean
import Kalman.Proofs.RealObservablePosterior
import Kalman.Proofs.FloatObservablePosterior
import Kalman.Proofs.RealObservableCorrection
import Kalman.Proofs.FloatObservableFilter
import Kalman.Proofs.FloatInputHorizon
import Kalman.Proofs.FloatDenseHorizon
import Kalman.Proofs.FloatFilterHorizon
import Kalman.Proofs.FloatFilterBudget
import Kalman.Proofs.FloatFilterDomain
import Kalman.Proofs.FloatObservableInitialization
import Kalman.Proofs.RealObservableHorizon
import Kalman.Proofs.FloatObservableHorizon
import Kalman.Proofs.FloatObservableDenseOutput
