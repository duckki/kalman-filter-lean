import Kalman.Implementation.CovarianceFilter
import Kalman.Implementation.SquareRootFilter

/-!
# Executable numerical regressions

Analytic scalar and 2×2 expectations, independent covariance formulas,
rectangular observations, repeated updates, QR Gram reconstruction, and API
rejections. Native observations are tests, not proofs of binary64 model behavior.
-/

namespace Kalman.Tests.FloatImplementations

open Kalman.Definitions.Input
open Kalman.Implementation.LinearAlgebra
open Kalman.Implementation

def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

def requireOk {α : Type} (value : Except Error α) (label : String) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"{label}: {repr error}")

def close (a b : Array Float) (tolerance : Float := 1.0e-11) : Bool :=
  a.size == b.size
  && (Array.range a.size).all
      fun i =>
        (a.getD i 0.0 - b.getD i 0.0).abs ≤ tolerance

def scalar (h r q : Float) : Model :=
  ⟨1, 1, #[1.0], #[h], #[q], #[r], #[2.0]⟩

def scalarChecks : IO Unit := do
  let input := scalar 1.0 1.0 1.0
  let initial : State := ⟨#[0.0], #[1.0]⟩
  for form in [CovarianceFilter.Form.compact, .subtractive, .joseph] do
    let corrected ←
      requireOk (CovarianceFilter.update form input initial) "scalar correction"
    check (close corrected.mean #[1.0]) "scalar posterior mean"
    check (close corrected.covariance #[0.5]) "scalar posterior covariance"
    let next ← requireOk (CovarianceFilter.step form input initial) "scalar full step"
    check (close next.mean #[4.0 / 3.0]) "predicted scalar mean"
    check (close next.covariance #[2.0 / 3.0]) "predicted scalar covariance"
  let factor ←
    requireOk (SquareRootFilter.fromCovariance input initial)
      "scalar factor initialization"
  let next ← requireOk (SquareRootFilter.step input factor) "scalar square-root step"
  let dense ←
    requireOk (SquareRootFilter.materialize 1 next) "scalar factor materialization"
  check (close dense.mean #[4.0 / 3.0] && close dense.covariance #[2.0 / 3.0])
    "square-root scalar analytic reference"

def correlatedChecks : IO Unit := do
  let input : Model :=
    ⟨2, 2, identity 2, identity 2, #[0.125, 0.0, 0.0, 0.125], identity 2, #[3.0, 0.0]⟩
  let initial : State := ⟨#[0.0, 0.0], #[2.0, 1.0, 1.0, 2.0]⟩
  for form in [CovarianceFilter.Form.compact, .subtractive, .joseph] do
    let result ←
      requireOk (CovarianceFilter.update form input initial) "correlated correction"
    check (close result.mean #[1.875, 0.375]) "correlated analytic mean"
    check (close result.covariance #[0.625, 0.125, 0.125, 0.625])
      "correlated analytic covariance"
  let factor ←
    requireOk (SquareRootFilter.fromCovariance input initial) "correlated initialization"
  let result ←
    requireOk (SquareRootFilter.update input factor) "correlated square-root correction"
  let dense ←
    requireOk (SquareRootFilter.materialize 2 result) "correlated materialization"
  check (close dense.mean #[1.875, 0.375]) "square-root correlated mean"
  check (close dense.covariance #[0.625, 0.125, 0.125, 0.625])
    "square-root correlated covariance"

def mixedObservationChecks : IO Unit := do
  let input : Model :=
    ⟨
      2,
      2,
      identity 2,
      #[1.0, 1.0, 0.0, 1.0],
      #[0.125, 0.0, 0.0, 0.125],
      #[1.0, 0.5, 0.5, 2.0],
      #[3.0, -1.0]
    ⟩
  let initial : State := ⟨#[0.0, 0.0], #[2.0, 1.0, 1.0, 2.0]⟩
  let expectedMean := #[116.0 / 63.0, 46.0 / 63.0]
  let expectedCovariance := #[38.0 / 63.0, -11.0 / 63.0, -11.0 / 63.0, 38.0 / 63.0]
  for form in [CovarianceFilter.Form.compact, .subtractive, .joseph] do
    let result ←
      requireOk (CovarianceFilter.update form input initial) "mixed observation"
    check (close result.mean expectedMean && close result.covariance expectedCovariance)
      "mixed observation analytic reference"
  let factor ←
    requireOk (SquareRootFilter.fromCovariance input initial) "mixed initialization"
  let result ← requireOk (SquareRootFilter.update input factor) "mixed square root"
  let dense ← requireOk (SquareRootFilter.materialize 2 result) "mixed materialization"
  check (close dense.mean expectedMean && close dense.covariance expectedCovariance)
    "square-root mixed observation analytic reference"

def rectangularChecks : IO Unit := do
  let base : Model :=
    ⟨2, 1, #[1.0, 1.0, 0.0, 1.0], #[1.0, 0.0], #[0.01, 0.0, 0.0, 0.01], #[0.5], #[1.0]⟩
  let initial : State := ⟨#[0.0, 1.0], #[2.0, 0.25, 0.25, 1.0]⟩
  let mut compact := initial
  let mut subtractive := initial
  let mut joseph := initial
  let mut factor ←
    requireOk (SquareRootFilter.fromCovariance base initial) "rectangular initialization"
  for k in [:100] do
    let input := { base with measurement := #[(k + 1).toFloat + 0.125] }
    compact ←
      requireOk (CovarianceFilter.step .compact input compact) "rectangular compact"
    subtractive ←
      requireOk (CovarianceFilter.step .subtractive input subtractive)
        "rectangular subtractive"
    joseph ← requireOk (CovarianceFilter.step .joseph input joseph) "rectangular Joseph"
    factor ← requireOk (SquareRootFilter.step input factor) "rectangular square root"
    let dense ←
      requireOk (SquareRootFilter.materialize 2 factor) "rectangular materialization"
    check
      (close compact.mean joseph.mean
        && close subtractive.mean joseph.mean
        && close dense.mean joseph.mean)
      "repeated rectangular means disagree"
    check
      (close compact.covariance joseph.covariance
        && close subtractive.covariance joseph.covariance
        && close dense.covariance joseph.covariance)
      "repeated rectangular covariances disagree"
    check (factor.validate 2 matches .ok ()) "invalid returned factor"

def qrChecks : IO Unit := do
  let a := #[1.0, 2.0, 3.0, 4.0, -2.0, 1.0]
  let l ←
    requireOk (Kalman.Implementation.OrthogonalFactorization.gramFactor 2 3 a)
      "rectangular QR"
  let reconstructed ← requireOk (multiply 2 2 2 l (transpose 2 2 l)) "QR reconstruction"
  check (close reconstructed #[14.0, 3.0, 3.0, 21.0]) "QR analytic Gram"
  let tiny := a.map fun x => x * 1.0e-200
  let tinyFactor ←
    requireOk (Kalman.Implementation.OrthogonalFactorization.gramFactor 2 3 tiny)
      "scaled QR underflow avoidance"
  check
    (tinyFactor.all Float.isFinite
      && 0.0 < tinyFactor.getD 0 0.0
      && 0.0 < tinyFactor.getD 3 0.0)
    "scaled QR lost factor rank"
  let tinyDense ←
    requireOk (SquareRootFilter.materialize 2 ⟨#[0.0, 0.0], tinyFactor⟩)
      "tiny materialization"
  check (tinyDense.covariance.all (fun x => x == 0.0))
    "positive tiny factor should materialize to zero by binary64 underflow"
  let rankDeficient := #[1.0, 0.0, 0.0, 0.0]
  check
    (Kalman.Implementation.OrthogonalFactorization.gramFactor 2 2 rankDeficient
      matches .error .nonpositivePivot)
    "rank-deficient QR accepted"

/-- Independent exact solution for a nonunit lower factor and two RHS columns.
This exercises both triangular passes and their post-subtraction divisions. -/
def choleskySolveChecks : IO Unit := do
  let l := #[2.0, 0.0, 1.0, 3.0]
  let b := #[10.0, 6.0, 32.0, -6.0]
  let y ← requireOk (forwardCholesky 2 2 l b) "Cholesky forward substitution"
  check (close y #[5.0, 3.0, 9.0, -3.0] 0.0) "Cholesky forward analytic reference"
  let x ← requireOk (solveCholesky 2 2 l b) "Cholesky two-pass solve"
  check (close x #[1.0, 2.0, 3.0, -1.0] 0.0) "Cholesky solve analytic reference"
  let factored ← requireOk (cholesky 2 #[4.0, 2.0, 2.0, 10.0]) "Cholesky analytic factor"
  check (close factored l 0.0) "Cholesky nonunit factor reference"
  check
    (divideResidual [] (fun _ => 0.0) (fun _ => 0.0) 1.0 0.0
      matches .error .nonfiniteComputation)
    "zero diagonal division accepted"

/-- Original-input Cholesky domain: diagonal endpoints/interiors, correlation
endpoints and every signed-zero pairing. Reconstruction is compared directly
with the original dense covariance; these native checks supplement the proof. -/
def choleskyInputDomainChecks : IO Unit := do
  let negativeZero := Float.ofBits 0x8000000000000000
  let offDiagonals : List (Float × Float) :=
    [
      (-0.25, -0.25),
      (0.25, 0.25),
      (0.0, 0.0),
      (negativeZero, negativeZero),
      (0.0, negativeZero),
      (negativeZero, 0.0)
    ]
  let input : Model := ⟨2, 2, identity 2, identity 2, identity 2, identity 2, #[0.0, 0.0]⟩
  for d0 in [1.0, 1.5, 2.0] do
    for d1 in [1.0, 1.5, 2.0] do
      for (upper, lower) in offDiagonals do
        let a := #[d0, upper, lower, d1]
        check (symmetric 2 a) "Cholesky input-domain symmetry, including signed zeros"
        let l ← requireOk (cholesky 2 a) "Cholesky input-domain success"
        check
          (l.size == 4
            && l.all Float.isFinite
            && l.getD 1 1.0 == 0.0
            && 0.75 ≤ l.getD 0 0.0
            && l.getD 0 0.0 ≤ 2.0
            && 0.75 ≤ l.getD 3 0.0
            && l.getD 3 0.0 ≤ 2.0
            && (l.getD 2 0.0).abs ≤ 0.5)
          "Cholesky input-domain factor enclosure"
        let reconstructed ←
          requireOk (multiply 2 2 2 l (transpose 2 2 l))
            "Cholesky input-domain Gram reconstruction"
        check (close reconstructed a 1.0e-14) "Cholesky input-domain original covariance"
        let initial : State := ⟨#[0.5, -1.0], a⟩
        let factor ←
          requireOk (SquareRootFilter.fromCovariance input initial)
            "Cholesky input-domain checked initialization"
        check (factor.validate 2 matches .ok ())
          "Cholesky input-domain initializer validation"
        check
          (factor.mean.map Float.toBits == initial.mean.map Float.toBits
            && factor.lower.map Float.toBits == l.map Float.toBits)
          "Cholesky input-domain initializer preserves native storage"

        let b := #[0.125, -0.125, -0.0625, 0.0625]
        let solved ←
          requireOk (solveCholesky 2 2 l b) "original covariance factor-and-solve"
        let determinant := d0 * d1 - lower * lower
        let expected :=
          #[
            (d1 * 0.125 + lower * 0.0625) / determinant,
            (-d1 * 0.125 - lower * 0.0625) / determinant,
            (-lower * 0.125 - d0 * 0.0625) / determinant,
            (lower * 0.125 + d0 * 0.0625) / determinant
          ]
        check (close solved expected 1.0e-13) "original covariance inverse reference"
        check (solved.all (fun v => v.abs ≤ 1.0)) "original covariance solution enclosure"

/-- Stored-factor solve domain, including its least diagonal and largest lower
entry. The reference uses the analytic inverse of the factor's Gram. -/
def choleskySolveDomainChecks : IO Unit := do
  let negativeZero := Float.ofBits 0x8000000000000000
  let rightHandSides :=
    [
      #[0.125, -0.125, -0.125, 0.125],
      #[0.0625, 0.125, -0.03125, -0.0625],
      #[0.0, negativeZero, negativeZero, 0.0]
    ]
  for d0 in [0.5, 1.0, 2.0] do
    for d1 in [0.5, 1.0, 2.0] do
      for c in [-2.0, 0.0, 2.0] do
        for upper in [0.0, negativeZero] do
          let l := #[d0, upper, c, d1]
          for b in rightHandSides do
            let y ← requireOk (forwardCholesky 2 2 l b) "solve-domain forward success"
            let x ← requireOk (solveCholesky 2 2 l b) "solve-domain two-pass success"
            check (y.size == 4 && y.all Float.isFinite && y.all (fun v => v.abs ≤ 3.0))
              "solve-domain forward enclosure"
            check (x.size == 4 && x.all Float.isFinite && x.all (fun v => v.abs ≤ 30.0))
              "solve-domain backward enclosure"
            let a00 := d0 * d0
            let a01 := d0 * c
            let a11 := c * c + d1 * d1
            let determinant := a00 * d1 * d1
            let expected :=
              #[
                (a11 * b.getD 0 0.0 - a01 * b.getD 2 0.0) / determinant,
                (a11 * b.getD 1 0.0 - a01 * b.getD 3 0.0) / determinant,
                (a00 * b.getD 2 0.0 - a01 * b.getD 0 0.0) / determinant,
                (a00 * b.getD 3 0.0 - a01 * b.getD 1 0.0) / determinant
              ]
            check (close x expected 1.0e-12) "solve-domain independent inverse reference"

/-- Independent 3-4-5 norm, unused prefix, extreme scaling, and rejection cases.
These validate the native extraction separately from its logical error theorem. -/
def qrNormChecks : IO Unit := do
  let x := #[1000.0, 3.0, 4.0]
  let (scale, v, norm) ←
    requireOk
      (OrthogonalFactorization.scaledColumnNorm 3 (List.range' 1 2) (x.getD · 0.0))
      "QR normalized tail norm"
  check (scale == 4.0 && norm == 1.25 && close v #[0.0, 0.75, 1.0] 0.0)
    "QR tail norm analytic reference"
  let tiny := Float.ofBits 0x0000000000000001
  let huge := Float.ofBits 0x7fefffffffffffff
  for a in [tiny, huge] do
    let (s, w, n) ←
      requireOk
        (OrthogonalFactorization.scaledColumnNorm 1 [0] (fun _ => a))
        "QR extreme finite norm"
    check (s == a && n == 1.0 && close w #[1.0] 0.0) "QR extreme scale reference"
  let (_, w, n) ←
    requireOk
      (OrthogonalFactorization.scaledColumnNorm 2 [0, 1] (#[huge, tiny].getD · 0.0))
      "QR normalized component underflow"
  check (n == 1.0 && close w #[1.0, 0.0] 0.0) "QR component underflow reference"
  check
    (OrthogonalFactorization.scaledColumnNorm 2 [0, 1] (fun _ => 0.0)
      matches .error .nonpositivePivot) "zero QR norm accepted"
  let nan := Float.ofBits 0x7ff8000000000000
  check
    (OrthogonalFactorization.scaledColumnNorm 2 [0, 1] (#[1.0, nan].getD · 0.0)
      matches .error .nonfiniteComputation) "exceptional QR norm accepted"

/-- Sign choice, analytic reflection, inactive storage, dimension boundary, and
rejection. The repeated-index check protects the original in-place schedule. -/
def qrReflectorChecks : IO Unit := do
  for sign in [1.0, -1.0] do
    let (alpha, w) ←
      requireOk (OrthogonalFactorization.householderReflector 0 [0] #[sign] 1.0)
        "scalar QR reflector"
    check (alpha == -sign && close w #[sign] 0.0) "scalar QR reflector reference"
  for zero in [0.0, Float.ofBits 0x8000000000000000] do
    let (alpha, w) ←
      requireOk (OrthogonalFactorization.householderReflector 0 [0, 1] #[zero, 1.0] 1.0)
        "signed-zero QR reflector"
    check (alpha.toBits == 0xbff0000000000000) "signed-zero reflector sign branch"
    check (close w #[0.7071067811865475, 0.7071067811865475] 1.0e-15)
      "signed-zero QR reflector reference"
  let (alpha, w) ←
    requireOk
      (OrthogonalFactorization.householderReflector 1 [1, 2] #[1000.0, 0.75, 1.0] 1.25)
      "QR reflector tail"
  check
    (alpha == -1.25 && close w #[1000.0, 0.8944271909999159, 0.4472135954999579] 1.0e-15)
    "QR reflector analytic vector and inactive prefix"
  let dot := 0.75 * w.getD 1 0.0 + w.getD 2 0.0
  check
    ((0.75 - 2.0 * w.getD 1 0.0 * dot + 1.25).abs < 1.0e-14
      && (1.0 - 2.0 * w.getD 2 0.0 * dot).abs < 1.0e-14)
    "QR reflector maps 3-4-5 tail to signed norm"
  let (_, boundary) ←
    requireOk
      (OrthogonalFactorization.householderReflector 0 (List.range 32)
        (Array.replicate 32 2.0) 6.0)
      "32-component QR reflector"
  let squared := boundary.foldl (fun s x => s + x * x) 0.0
  check ((squared - 1.0).abs < 1.0e-12) "32-component reflector unit norm"
  let repeated ←
    requireOk (OrthogonalFactorization.normalizeVector [0, 0] #[4.0] 2.0)
      "repeated normalization schedule"
  check (close repeated #[1.0] 0.0) "normalization must read the overwritten component"
  check
    (OrthogonalFactorization.householderReflector 0 [0] #[0.0] 0.0
      matches .error .nonpositivePivot)
    "zero reflector norm accepted"
  check
    (OrthogonalFactorization.householderReflector 0 [0, 1] #[1.0, Float.nan] 1.0
      matches .error .nonfiniteComputation)
    "exceptional reflector component accepted"

/-- Analytic column reflection, untouched slots, domain extremes, repeated
mutable reads, and rejection. These exercise the helper used by actual QR. -/
def qrApplicationChecks : IO Unit := do
  let negativeZero := Float.ofBits 0x8000000000000000
  let a := #[1.0, 2000.0, negativeZero, 2.0, 3.0, 4.0, 5.0, 4.0, 6.0]
  let output ←
    requireOk (OrthogonalFactorization.applyReflector 3 1 [1, 2] #[0.0, 0.6, 0.8] a)
      "QR analytic column reflection"
  check (close output #[1.0, 2000.0, negativeZero, 2.0, -3.0, 4.0, 5.0, -4.0, 6.0] 0.0)
    "QR analytic column reflection reference"
  check ((output.getD 2 0.0).toBits == negativeZero.toBits)
    "QR inactive signed zero changed"
  let x := #[1000.0, 3.0, 4.0]
  let (_, v, norm) ←
    requireOk (OrthogonalFactorization.scaledColumnNorm 3 [1, 2] (x.getD · 0.0))
      "QR application source norm"
  let (_, w) ←
    requireOk (OrthogonalFactorization.householderReflector 1 [1, 2] v norm)
      "QR application source reflector"
  let reflected ←
    requireOk (OrthogonalFactorization.applyReflector 1 0 [1, 2] w x)
      "QR three-stage source reflection"
  check (close reflected #[1000.0, -5.0, 0.0] 1.0e-14) "QR three-stage 3-4-5 reference"
  for x
      in [
        Float.ofBits 0x7830000000000000,
        Float.ofBits 0x0010000000000000,
        Float.ofBits 0x0000000000000001
      ] do
    let result ←
      requireOk (OrthogonalFactorization.applyReflector 1 0 [0] #[1.0] #[x])
        "QR application large, normal-minimum, or subnormal input"
    check ((result.getD 0 0.0).toBits == (-x).toBits) "QR extreme reflection reference"
  let boundary ←
    requireOk
      (OrthogonalFactorization.applyReflector 1 0 (List.range 32)
        (Array.replicate 32 2.0) (Array.replicate 32 1.0))
      "QR 32-component application"
  check (close boundary (Array.replicate 32 (-255.0)) 0.0)
    "QR 32-component analytic rank-one update"
  let repeated ←
    requireOk (OrthogonalFactorization.applyReflector 1 0 [0, 0] #[1.0] #[4.0])
      "QR repeated application schedule"
  check (close repeated #[-28.0] 0.0) "QR application must read the overwritten slot"
  let empty ←
    requireOk (OrthogonalFactorization.applyReflector 3 1 [] #[] a)
      "QR empty application schedule"
  check (close empty a 0.0 && (empty.getD 2 0.0).toBits == negativeZero.toBits)
    "QR empty application changed storage"
  check
    (OrthogonalFactorization.applyReflector 1 0 [0] #[1.0] #[Float.nan]
      matches .error .nonfiniteComputation)
    "exceptional application input accepted"
  check
    (OrthogonalFactorization.applyReflector 1 0 [0] #[2.0]
        #[Float.ofBits 0x7fefffffffffffff]
      matches .error .nonfiniteComputation)
    "overflowing application accepted"

/-- Source-column finishing: analytic norm, sign branches, exact positive-zero
writes, preserved slots, scale-domain endpoints and exceptional rescaling. -/
def qrFinishChecks : IO Unit := do
  let negativeZero := Float.ofBits 0x8000000000000000
  let a := #[1.0, 2000.0, negativeZero, 2.0, 3.0, 4.0, 5.0, 4.0, 6.0]
  let (scale, v, norm) ←
    requireOk (OrthogonalFactorization.scaledColumnNorm 3 [1, 2] (fun i => entry 3 a i 1))
      "QR finish source norm"
  let (alpha, w) ←
    requireOk (OrthogonalFactorization.householderReflector 1 [1, 2] v norm)
      "QR finish source reflector"
  let output ←
    requireOk (OrthogonalFactorization.finishColumn 3 1 1 [2] a alpha scale)
      "QR source finish"
  check (entry 3 output 1 1 == -5.0 && (entry 3 output 2 1).toBits == 0)
    "QR finished 3-4-5 reference"
  for t in [:a.size] do
    if t != 4 && t != 7 then
      check ((output.getD t 0.0).toBits == (a.getD t 0.0).toBits)
        "QR finish changed an unvisited slot"
  let reflected ←
    requireOk (OrthogonalFactorization.applyReflector 3 1 [1, 2] w a)
      "QR source reflector comparison"
  check
    ((entry 3 reflected 1 1 + 5.0).abs < 1.0e-14 && (entry 3 reflected 2 1).abs < 1.0e-14)
    "QR finish versus reflected source"
  for x in [Float.ofBits 0x07b0000000000000, Float.ofBits 0x7830000000000000] do
    for sign in [1.0, -1.0] do
      let input := #[sign * x]
      let (s, v, n) ←
        requireOk (OrthogonalFactorization.scaledColumnNorm 1 [0] (input.getD · 0.0))
          "QR finish scale endpoint norm"
      let (alpha, _) ←
        requireOk (OrthogonalFactorization.householderReflector 0 [0] v n)
          "QR finish scale endpoint reflector"
      let result ←
        requireOk (OrthogonalFactorization.finishColumn 1 0 0 [] input alpha s)
          "QR finish scale endpoint"
      check
        ((result.getD 0 0.0).toBits == (-sign * x).toBits
          && (result.getD 0 0.0).isFinite
          && 0.0 < (result.getD 0 0.0).abs)
        "QR finish scale endpoint diagonal reference"
  for zero in [0.0, negativeZero] do
    let input := #[zero, 1.0]
    let (s, v, n) ←
      requireOk (OrthogonalFactorization.scaledColumnNorm 2 [0, 1] (input.getD · 0.0))
        "QR finish signed-zero source norm"
    let (alpha, _) ←
      requireOk (OrthogonalFactorization.householderReflector 0 [0, 1] v n)
        "QR finish signed-zero source reflector"
    let result ←
      requireOk (OrthogonalFactorization.finishColumn 1 0 0 [1] input alpha s)
        "QR finish signed-zero source"
    check
      ((result.getD 0 0.0).toBits == (-1.0 : Float).toBits
        && (result.getD 1 0.0).toBits == 0)
      "QR finish signed-zero sign and tail reference"
  let ones := Array.replicate 32 1.0
  let (s, v, n) ←
    requireOk
      (OrthogonalFactorization.scaledColumnNorm 32 (List.range 32) (ones.getD · 0.0))
      "QR finish 32-row source norm"
  let (alpha, _) ←
    requireOk (OrthogonalFactorization.householderReflector 0 (List.range 32) v n)
      "QR finish 32-row source reflector"
  let boundary ←
    requireOk (OrthogonalFactorization.finishColumn 1 0 0 (List.range' 1 31) ones alpha s)
      "QR finish 32-row source"
  let diagonal := boundary.getD 0 0.0
  check
    (diagonal < 0.0
      && (diagonal * diagonal - 32.0).abs < 1.0e-11
      && (List.range' 1 31).all (fun i => (boundary.getD i 0.0).toBits == 0))
    "QR finish 32-row squared norm and positive-zero reference"
  let zeros ←
    requireOk
      (OrthogonalFactorization.finishColumn 1 0 0 [1, 1] #[3.0, negativeZero] (-1.0) 2.0)
      "QR finish repeated zero write"
  check (close zeros #[-2.0, 0.0] 0.0 && (zeros.getD 1 0.0).toBits == 0)
    "QR finish zero writes must be positive and idempotent"
  check
    (OrthogonalFactorization.finishColumn 1 0 0 [] #[1.0] 6.0
        (Float.ofBits 0x7fefffffffffffff)
      matches .error .nonfiniteComputation)
    "overflowing diagonal rescaling accepted"
  check
    (OrthogonalFactorization.finishColumn 1 0 0 [] #[1.0] Float.nan 1.0
      matches .error .nonfiniteComputation)
    "exceptional diagonal rescaling accepted"

/-- One complete QR iteration against the analytic 3-4-5 Householder matrix,
plus copied prefixes, another pivot, column-count extremes and rejection. -/
def qrIterationChecks : IO Unit := do
  let negativeZero := Float.ofBits 0x8000000000000000
  let a := #[11.0, negativeZero, 13.0, 14.0, 21.0, 3.0, 8.0, 1.0, 31.0, 4.0, 6.0, 2.0]
  let output ←
    requireOk (OrthogonalFactorization.qrIteration 3 4 1 a) "QR complete iteration"
  -- The exact active reflector is [[-3/5, -4/5], [-4/5, 3/5]].
  check
    (close output
      #[
        11.0,
        negativeZero,
        13.0,
        14.0,
        21.0,
        -5.0,
        -9.6,
        -2.2,
        31.0,
        0.0,
        -2.8,
        0.4
      ]
      1.0e-13)
    "QR analytic iteration reference"
  for t in [0, 1, 2, 3, 4, 8] do
    check ((output.getD t 0.0).toBits == (a.getD t 0.0).toBits)
      "QR copied iteration prefix"
  check ((entry 4 output 2 1).toBits == 0)
    "QR complete iteration tail must be positive zero"
  let second ←
    requireOk (OrthogonalFactorization.qrIteration 3 4 2 output) "QR next analytic pivot"
  check
    ((entry 4 second 2 2 - 2.8).abs < 1.0e-13 && (entry 4 second 2 3 + 0.4).abs < 1.0e-13)
    "QR second iteration analytic reference"
  for t in [:output.size] do
    if t != 10 && t != 11 then
      check ((second.getD t 0.0).toBits == (output.getD t 0.0).toBits)
        "QR later iteration changed earlier columns or prefix"
  for sign in [1.0, -1.0] do
    let lastInput := #[negativeZero, 2.0, 3.0, sign * 4.0]
    let last ←
      requireOk (OrthogonalFactorization.qrIteration 2 2 1 lastInput)
        "QR final singleton iteration"
    check
      (close last #[negativeZero, 2.0, 3.0, -sign * 4.0] 0.0
        && (last.getD 0 0.0).toBits == negativeZero.toBits)
      "QR singleton iteration reference"
  let wide := (Array.range 65).map (fun i => (i + 1).toFloat)
  let wideOutput ←
    requireOk (OrthogonalFactorization.qrIteration 1 65 0 wide)
      "QR one-row 65-column iteration"
  check (close wideOutput (wide.map fun x => -x) 0.0)
    "QR column count must not limit local row bound"
  let ones := Array.replicate 32 1.0
  let tall := ones.flatMap (fun x => #[x, 2.0 * x])
  let tallOutput ←
    requireOk (OrthogonalFactorization.qrIteration 32 2 0 tall) "QR 32-row iteration"
  let root := (32.0 : Float).sqrt
  check
    ((entry 2 tallOutput 0 0 + root).abs < 1.0e-13
      && (entry 2 tallOutput 0 1 + 2.0 * root).abs < 1.0e-12)
    "QR 32-row parallel-column head reference"
  for i in [1:32] do
    check ((entry 2 tallOutput i 0).toBits == 0 && (entry 2 tallOutput i 1).abs < 1.0e-12)
      "QR 32-row parallel-column tail reference"
  let repeated ←
    requireOk
      (OrthogonalFactorization.applyReflectorColumns 2 [1, 1] [0] #[1.0] #[7.0, 3.0])
      "QR repeated column schedule"
  check (close repeated #[7.0, 3.0] 0.0)
    "QR repeated columns must read the updated matrix"
  check
    (OrthogonalFactorization.qrIteration 2 2 0 #[0.0, 3.0, 0.0, 4.0]
      matches .error .nonpositivePivot)
    "zero iteration source accepted"
  check
    (OrthogonalFactorization.qrIteration 2 3 0 #[3.0, 8.0, Float.nan, 4.0, 6.0, 7.0]
      matches .error .nonfiniteComputation)
    "exceptional later trailing column accepted"

/-- Full QR structure: independent analytic tall reference, exact assigned zeros,
column-copy invariants, and retained/full stored Gram reconstruction. -/
def qrTriangularChecks : IO Unit := do
  let analytic := #[3.0, 0.0, 4.0, 0.0, 0.0, 2.0]
  let r ←
    requireOk (OrthogonalFactorization.triangularize 3 2 analytic) "QR analytic tall loop"
  check (close r #[-5.0, 0.0, 0.0, -2.0, 0.0, 0.0] 0.0)
    "QR analytic tall triangular result"
  for i in [:3] do
    for j in [:2] do
      if j < i then
        check ((entry 2 r i j).toBits == 0)
          "QR full tall lower triangle must be positive zero"
  let factor ←
    requireOk (OrthogonalFactorization.gramFactor 2 3 #[3.0, 4.0, 0.0, 0.0, 0.0, 2.0])
      "QR analytic tall factor"
  check (close factor #[5.0, 0.0, 0.0, 2.0] 0.0) "QR analytic full factor reference"
  let rgram ←
    requireOk (multiply 2 3 2 (transpose 3 2 r) r) "QR analytic full stored column Gram"
  check (close rgram #[25.0, 0.0, 0.0, 4.0] 0.0) "QR full stored Gram analytic reference"
  let a := #[2.0, 1.0, 0.0, 1.0, 3.0, 1.0, 0.0, 1.0, 2.0, 1.0, 0.0, 1.0]
  let mut manual := a
  for pivot in [:3] do
    let before := manual
    manual ←
      requireOk (OrthogonalFactorization.qrIteration 4 3 pivot manual)
        "QR structural pivot"
    check (manual.size == 12 && manual.all Float.isFinite) "QR structural storage"
    for j in [:pivot] do
      for i in [:4] do
        check ((entry 3 manual i j).toBits == (entry 3 before i j).toBits)
          "QR later pivot changed an earlier stored column"
    for j in [:pivot + 1] do
      for i in [j + 1:4] do
        check ((entry 3 manual i j).toBits == 0) "QR processed-column zero invariant"
  let complete ←
    requireOk (OrthogonalFactorization.triangularize 4 3 a) "QR complete tall loop"
  check (complete.toList.map Float.toBits == manual.toList.map Float.toBits)
    "QR ascending extracted loop schedule"
  let l ←
    requireOk (OrthogonalFactorization.retainFactor 3 complete)
      "QR complete retained factor"
  let fullGram ←
    requireOk (multiply 3 4 3 (transpose 4 3 complete) complete) "QR full column Gram"
  let retainedGram ←
    requireOk (multiply 3 3 3 l (transpose 3 3 l)) "QR retained factor Gram"
  check (close retainedGram fullGram 1.0e-12) "QR retained/full stored Gram agreement"
  let boundary ←
    requireOk (OrthogonalFactorization.triangularize 33 33 (identity 33))
      "QR structural guarantee beyond numerical-profile dimension cap"
  for i in [:33] do
    for j in [:33] do
      check (entry 33 boundary i j == if i == j then -1.0 else 0.0)
        "QR 33-dimensional analytic diagonal reflection"
      if j < i then
        check ((entry 33 boundary i j).toBits == 0) "QR 33-dimensional assigned zeros"
  let empty ←
    requireOk (OrthogonalFactorization.triangularize 4 0 #[]) "QR zero-column loop"
  check (empty.isEmpty) "QR empty column range output"
  check
    (OrthogonalFactorization.triangularize 2 2 #[0.0, 1.0, 0.0, 1.0]
      matches .error .nonpositivePivot)
    "QR first-pivot zero rejection"
  check
    (OrthogonalFactorization.triangularize 2 2 #[1.0, 0.0, 0.0, 0.0]
      matches .error .nonpositivePivot)
    "QR later-pivot zero rejection"
  check
    (OrthogonalFactorization.triangularize 2 2 #[1.0, Float.nan, 0.0, 1.0]
      matches .error .nonfiniteComputation)
    "QR full-loop exceptional trailing product"

/-- A later pivot with valid prior zeros preserves an independent analytic Gram.
The contrasting input shows why prior-zero structure is needed for full Gram claims. -/
def qrGramChecks : IO Unit := do
  let a := #[-5.0, 1.0, 2.0, 0.0, 3.0, 1.0, 0.0, 4.0, 2.0, 0.0, 0.0, 3.0]
  let reference := #[25.0, -5.0, -10.0, -5.0, 26.0, 13.0, -10.0, 13.0, 18.0]
  let before ← requireOk (multiply 3 4 3 (transpose 4 3 a) a) "QR incoming analytic Gram"
  check (close before reference 0.0) "QR incoming Gram independent reference"
  let output ←
    requireOk (OrthogonalFactorization.qrIteration 4 3 1 a) "QR later-pivot Gram"
  let after ←
    requireOk (multiply 3 4 3 (transpose 4 3 output) output) "QR outgoing stored Gram"
  check (close after reference 1.0e-12) "QR later-pivot analytic Gram preservation"
  for i in [:4] do
    check ((entry 3 output i 0).toBits == (entry 3 a i 0).toBits)
      "QR Gram comparison must preserve earlier column"
  for j in [:3] do
    check ((entry 3 output 0 j).toBits == (entry 3 a 0 j).toBits)
      "QR Gram comparison must preserve prefix row"
  let invalid := #[1.0, 0.0, 1.0, 1.0]
  let changed ←
    requireOk (OrthogonalFactorization.qrIteration 2 2 1 invalid) "QR prior-zero contrast"
  check (close changed #[1.0, 0.0, 1.0, -1.0] 0.0) "QR prior-zero contrast output"
  let invalidBefore ←
    requireOk (multiply 2 2 2 (transpose 2 2 invalid) invalid)
      "QR prior-zero contrast incoming Gram"
  let invalidAfter ←
    requireOk (multiply 2 2 2 (transpose 2 2 changed) changed)
      "QR prior-zero contrast outgoing Gram"
  check (entry 2 invalidBefore 0 1 == 1.0 && entry 2 invalidAfter 0 1 == -1.0)
    "QR full Gram claim cannot omit the prior-zero hypothesis"

/-- Full retained-factor Gram against an independent correlated original-prearray
reference. Power-of-two rescaling exercises the quadratic error-budget scale. -/
def qrCompositionChecks : IO Unit := do
  let original :=
    #[2.0, 1.0, 0.0, 1.0, 0.0, 1.0, 3.0, 1.0, 0.0, 1.0, 0.0, 1.0, 2.0, 1.0, 1.0]
  let reference := #[6.0, 5.0, 2.0, 5.0, 12.0, 6.0, 2.0, 6.0, 7.0]
  for scale in [1.0, 1048576.0, 1.0 / 1048576.0] do
    let a := original.map (fun x => x * scale)
    let expected := reference.map (fun x => x * scale * scale)
    let tolerance := 1.0e-12 * scale * scale
    let incoming ←
      requireOk (multiply 3 5 3 a (transpose 3 5 a)) "QR original prearray Gram"
    check (close incoming expected 0.0) "QR original Gram independent analytic reference"
    let mut r := transpose 3 5 a
    for pivot in [:3] do
      r ←
        requireOk (OrthogonalFactorization.qrIteration 5 3 pivot r)
          "QR accumulated Gram pivot"
      let prefixGram ←
        requireOk (multiply 3 5 3 (transpose 5 3 r) r) "QR prefix stored Gram"
      check (close prefixGram expected tolerance)
        "QR prefix Gram against original analytic input"
      for j in [:pivot + 1] do
        check (0.0 < (entry 3 r j j).abs) "QR earlier diagonal remains nonzero"
    let l ←
      requireOk (OrthogonalFactorization.gramFactor 3 5 a) "QR original-input factor"
    check (l.size == 9 && l.all Float.isFinite) "QR full retained factor storage"
    for i in [:3] do
      check (0.0 < entry 3 l i i) "QR full retained positive diagonal"
      for j in [i + 1:3] do
        check ((entry 3 l i j).toBits == 0) "QR full retained upper zeros"
    let actual ←
      requireOk (multiply 3 3 3 l (transpose 3 3 l)) "QR complete retained Gram"
    check (close actual expected tolerance)
      "QR complete factor Gram against original input"
  let empty ← requireOk (OrthogonalFactorization.gramFactor 0 5 #[]) "QR no-pivot factor"
  check (empty.isEmpty) "QR zero-pivot composition"

/-- Source-tail headroom on a correlated eight-row tall input at the proposed
domain's scale endpoints. Dense Gram products would underflow/overflow there;
these checks use the stored factors and active entries directly. -/
def qrSourceTailChecks : IO Unit := do
  let original :=
    #[
      1.0,
      0.25,
      0.0,
      0.25,
      0.0,
      0.0,
      0.0,
      0.0,
      0.25,
      1.0,
      0.0,
      0.0,
      0.25,
      0.0,
      0.0,
      0.0,
      0.0,
      0.0,
      1.0,
      0.25,
      0.25,
      0.0,
      0.0,
      0.0
    ]
  let initialGram ←
    requireOk (multiply 3 8 3 original (transpose 3 8 original))
      "QR source fixture analytic Gram"
  check
    (close initialGram #[1.125, 0.5, 0.0625, 0.5, 1.125, 0.0625, 0.0625, 0.0625, 1.125]
      0.0)
    "QR source fixture independent Gram reference"
  let kernelFloor := Float.ofBits 0x07b0000000000000 -- 2^-900
  for scale in [1.0, Float.ofBits 0x07e0000000000000, Float.ofBits 0x7820000000000000] do
    -- scale = 1, 2^-897, 2^899; M = 2 * scale.
    let budget := 2.0 * scale
    let threshold := budget / 16.0
    check (0.0 < threshold && kernelFloor ≤ threshold) "QR source threshold scale floor"
    let a := original.map (fun x => x * scale)
    let mut current := transpose 3 8 a
    for pivot in [:3] do
      check (current.size == 24 && current.all Float.isFinite)
        "QR source-prefix finite storage"
      let mut maximum : Float := 0.0
      for i in [pivot:8] do
        let source := (entry 3 current i pivot).abs
        if maximum < source then maximum := source
        for j in [pivot:3] do
          check ((entry 3 current i j).abs ≤ budget) "QR prefix panel magnitude budget"
      check (threshold ≤ maximum) "QR active source entry M/16 witness"
      for j in [:pivot] do
        check (0.0 < (entry 3 current j j).abs) "QR prefix nonzero leading diagonal"
        for i in [j + 1:8] do
          check ((entry 3 current i j).toBits == 0) "QR source-tail prior column zeros"
      current ←
        requireOk (OrthogonalFactorization.qrIteration 8 3 pivot current)
          "QR source-domain pivot"
    let l ←
      requireOk (OrthogonalFactorization.gramFactor 3 8 a) "QR source-domain full factor"
    check (l.size == 9 && l.all Float.isFinite) "QR source-domain factor storage"
    for j in [:3] do
      check (0.0 < entry 3 l j j) "QR source-domain factor positive diagonal"

/-- All eight pivots at the dimension and scale boundaries of the initial-input
domain. The exact reference is a scaled identity factor, without a dense Gram
product that would underflow or overflow at the extreme scales. -/
def qrInitialDomainChecks : IO Unit := do
  for n in [:9] do
    for scale
        in [1.0, Float.ofBits 0x07e0000000000000, Float.ofBits 0x7820000000000000] do
      -- M = 2 * scale ranges from 2^-896 to 2^900.
      let a := (identity n).map (fun x => x * scale)
      let l ←
        requireOk (OrthogonalFactorization.gramFactor n n a) "QR initial-domain identity"
      check (l.size == n * n && l.all Float.isFinite) "QR initial-domain factor storage"
      check (close l a 0.0) "QR initial-domain exact scaled identity factor"
      for j in [:n] do
        check (0.0 < entry n l j j) "QR initial-domain positive diagonal"

/-- Innovation QR to solve, with correlated noise, nonzero observation blocks
and signed-zero RHS entries. Analytic two-state inverses provide independent
references for the stored factor Gram and original stored prearray Gram. -/
def qrFactorSolveDomainChecks : IO Unit := do
  let negativeZero := Float.ofBits 0x8000000000000000
  for d0 in [1.0, 1.5] do
    for d1 in [1.0, 1.5] do
      for c in [-0.25, 0.0, 0.25] do
        let tr ← requireOk (cholesky 2 #[d0, c, c, d1]) "innovation noise factor"
        for hl
            in [
              #[0.0, 0.0, 0.0, 0.0],
              #[0.125, 0.0, 0.125, 0.125],
              #[-0.125, 0.125, 0.125, -0.125]
            ] do
          let a := fromCols 2 2 2 tr hl
          let l ←
            requireOk (OrthogonalFactorization.gramFactor 2 4 a) "innovation QR factor"
          check (l.size == 4 && l.all Float.isFinite && entry 2 l 0 1 == 0.0)
            "innovation QR factor storage"
          check
            ((Array.range 2).all (fun i => 0.5 ≤ entry 2 l i i)
              && l.all (fun v => v.abs ≤ 2.0))
            "innovation QR solve factor bounds"
          let nativeG :=
            #[
              entry 2 l 0 0 * entry 2 l 0 0,
              entry 2 l 0 0 * entry 2 l 1 0,
              entry 2 l 1 0 * entry 2 l 0 0,
              entry 2 l 1 0 * entry 2 l 1 0 + entry 2 l 1 1 * entry 2 l 1 1
            ]
          let originalG :=
            (Array.range 4).map
              fun k =>
                let i := k / 2
                let j := k % 2
                ((List.range 4).map (fun t => entry 4 a i t * entry 4 a j t)).foldl
                  (· + ·) 0.0
          for b
              in [
                #[0.125, -0.125, -0.125, 0.125],
                #[0.0625, -0.0625, -0.03125, 0.03125],
                #[0.0, negativeZero, negativeZero, 0.0]
              ] do
            let y ← requireOk (forwardCholesky 2 2 l b) "innovation QR forward solve"
            let x ← requireOk (solveCholesky 2 2 l b) "innovation QR complete solve"
            check
              (y.size == 4 && y.all Float.isFinite && x.size == 4 && x.all Float.isFinite)
              "innovation QR solve storage"
            check (x.all (fun v => v.abs ≤ 1.0)) "innovation QR solution bound"
            for (g, tolerance)
                in [(nativeG, 7.275957614183426e-12), (originalG, 9.5367431640625e-7)] do
              let determinant :=
                entry 2 g 0 0 * entry 2 g 1 1 - entry 2 g 0 1 * entry 2 g 1 0
              let expected :=
                (Array.range 4).map
                  fun k =>
                    let j := k % 2
                    if k / 2 == 0 then
                      (entry 2 g 1 1 * entry 2 b 0 j - entry 2 g 0 1 * entry 2 b 1 j)
                      / determinant
                    else
                      (-entry 2 g 1 0 * entry 2 b 0 j + entry 2 g 0 0 * entry 2 b 1 j)
                      / determinant
              check (close x expected tolerance)
                "innovation QR independent inverse reference"

/-- Formed gain inputs: covariance-level RHS enclosure and gain magnitude,
including nonzero observations, correlated prior factors and upper signed zero.
Independent two-state covariance/innovation formulas give the gain reference. -/
def gainInputDomainChecks : IO Unit := do
  let negativeZero := Float.ofBits 0x8000000000000000
  for d0 in [0.5, 1.0, 1.25] do
    for d1 in [0.5, 1.0, 1.25] do
      for c in [-0.25, 0.0, 0.25] do
        for upper in [0.0, negativeZero] do
          let l := #[d0, upper, c, d1]
          for h
              in [
                #[0.0, 0.0, 0.0, 0.0],
                #[0.015625, 0.0, 0.0, 0.015625],
                #[0.015625, -0.015625, 0.015625, 0.015625]
              ] do
            let hl ← requireOk (multiply 2 2 2 h l) "gain formed HL"
            let pht ← requireOk (multiply 2 2 2 l (transpose 2 2 hl)) "gain formed PHT"
            let b := transpose 2 2 pht
            check (b.size == 4 && b.all Float.isFinite && b.all (fun v => v.abs ≤ 0.125))
              "gain formed RHS bounds"
            let s ←
              requireOk
                (OrthogonalFactorization.gramFactor 2 4 (fromCols 2 2 2 (identity 2) hl))
                "gain innovation factor"
            let x ← requireOk (solveCholesky 2 2 s b) "gain formed solve"
            let k := transpose 2 2 x
            check
              (k.size == 4 && k.all Float.isFinite && k.all (fun v => v.abs ≤ 1.0 / 3.0))
              "gain sharper magnitude"
            let p00 := d0 * d0
            let p01 := d0 * c
            let p11 := c * c + d1 * d1
            let c00 := p00 * entry 2 h 0 0 + p01 * entry 2 h 0 1
            let c01 := p00 * entry 2 h 1 0 + p01 * entry 2 h 1 1
            let c10 := p01 * entry 2 h 0 0 + p11 * entry 2 h 0 1
            let c11 := p01 * entry 2 h 1 0 + p11 * entry 2 h 1 1
            check (close pht #[c00, c01, c10, c11] 7.105427357601002e-14)
              "gain original stored covariance RHS reference"
            let s00 := 1.0 + entry 2 h 0 0 * c00 + entry 2 h 0 1 * c10
            let s01 := entry 2 h 0 0 * c01 + entry 2 h 0 1 * c11
            let s11 := 1.0 + entry 2 h 1 0 * c01 + entry 2 h 1 1 * c11
            let det := s00 * s11 - s01 * s01
            let expected :=
              #[
                (c00 * s11 - c01 * s01) / det,
                (-c00 * s01 + c01 * s00) / det,
                (c10 * s11 - c11 * s01) / det,
                (-c10 * s01 + c11 * s00) / det
              ]
            check (close k expected 1.0e-12)
              "gain independent original covariance reference"

/-- Original noise diagonal headroom, formed HL energy, and innovation/gain
stages with correlated noise. Independent dense scalar expressions include
the original noise covariance, rather than treating its factor as exact. -/
def innovationInputDomainChecks : IO Unit := do
  let negativeZero := Float.ofBits 0x8000000000000000
  for r0 in [1.0, 1.5] do
    for r1 in [1.0, 1.5] do
      for rc in [-0.25, 0.0, 0.25] do
        let tr ← requireOk (cholesky 2 #[r0, rc, rc, r1]) "innovation input noise"
        for l
            in [
              #[1.0, 0.0, 0.125, 1.0],
              #[1.25, negativeZero, -0.25, 1.25],
              #[0.5, 0.0, 0.25, 1.0]
            ] do
          for h
              in [
                #[0.0, 0.0, 0.0, 0.0],
                #[0.015625, 0.0, 0.0, 0.015625],
                #[0.015625, -0.015625, 0.015625, 0.015625]
              ] do
            let hl ← requireOk (multiply 2 2 2 h l) "innovation input observation block"
            check (hl.all (fun v => v.abs ≤ 0.125)) "innovation observation block bound"
            let a := fromCols 2 2 2 tr hl
            for i in [:2] do
              let energy :=
                ((List.range 4).map
                  (fun j =>
                    let v := entry 4 a i j;
                    v * v)).foldl
                  (· + ·) 0.0
              check (energy ≤ 2.0) "innovation prearray energy headroom"
            let s ←
              requireOk (OrthogonalFactorization.gramFactor 2 4 a) "innovation input QR"
            check
              (s.all Float.isFinite
                && s.all (fun v => v.abs ≤ 2.0)
                && 0.5 ≤ entry 2 s 0 0
                && 0.5 ≤ entry 2 s 1 1)
              "innovation input QR factor solve domain"
            let pht ←
              requireOk (multiply 2 2 2 l (transpose 2 2 hl)) "innovation input RHS"
            check (pht.all (fun v => v.abs ≤ 0.125)) "innovation input formed RHS bound"
            let x ←
              requireOk (solveCholesky 2 2 s (transpose 2 2 pht))
                "innovation input gain solve"
            let k := transpose 2 2 x
            check (k.all Float.isFinite && k.all (fun v => v.abs ≤ 1.0 / 3.0))
              "innovation input sharper gain bound"
            let d0 := entry 2 l 0 0
            let c := entry 2 l 1 0
            let d1 := entry 2 l 1 1
            let p00 := d0 * d0
            let p01 := d0 * c
            let p11 := c * c + d1 * d1
            let c00 := p00 * entry 2 h 0 0 + p01 * entry 2 h 0 1
            let c01 := p00 * entry 2 h 1 0 + p01 * entry 2 h 1 1
            let c10 := p01 * entry 2 h 0 0 + p11 * entry 2 h 0 1
            let c11 := p01 * entry 2 h 1 0 + p11 * entry 2 h 1 1
            let s00 := r0 + entry 2 h 0 0 * c00 + entry 2 h 0 1 * c10
            let s01 := rc + entry 2 h 0 0 * c01 + entry 2 h 0 1 * c11
            let s11 := r1 + entry 2 h 1 0 * c01 + entry 2 h 1 1 * c11
            let det := s00 * s11 - s01 * s01
            let expected :=
              #[
                (c00 * s11 - c01 * s01) / det,
                (-c00 * s01 + c01 * s00) / det,
                (c10 * s11 - c11 * s01) / det,
                (-c10 * s01 + c11 * s00) / det
              ]
            check (close k expected 1.0e-12)
              "innovation input original noise gain reference"
            for (mu, z)
                in [
                  (#[0.0625, -0.0625], #[1.0, -1.0]),
                  (#[-0.0625, 0.0625], #[-1.0, 1.0]),
                  (#[0.0, negativeZero], #[negativeZero, 0.0])
                ] do
              let input : Model := ⟨2, 2, identity 2, h, identity 2, #[r0, rc, rc, r1], z⟩
              let output ←
                requireOk (SquareRootFilter.updateUnchecked input ⟨mu, l⟩)
                  "local correction original-input execution"
              check
                (output.mean.size == 2
                  && output.mean.all Float.isFinite
                  && output.mean.all (fun v => v.abs ≤ 1.0))
                "local correction mean invariant"
              let residual0 :=
                z.getD 0 0.0
                - (entry 2 h 0 0 * mu.getD 0 0.0 + entry 2 h 0 1 * mu.getD 1 0.0)
              let residual1 :=
                z.getD 1 0.0
                - (entry 2 h 1 0 * mu.getD 0 0.0 + entry 2 h 1 1 * mu.getD 1 0.0)
              let reference :=
                #[
                  mu.getD 0 0.0
                  + entry 2 expected 0 0 * residual0
                  + entry 2 expected 0 1 * residual1,
                  mu.getD 1 0.0
                  + entry 2 expected 1 0 * residual0
                  + entry 2 expected 1 1 * residual1
                ]
              check (close output.mean reference 1.0e-12)
                "local correction independent ideal-gain mean"

/-- Stored-gain mean evaluation with sign cancellation, input endpoints,
signed zero and subnormal inputs. Scalar expressions provide the reference. -/
def meanInputDomainChecks : IO Unit := do
  let negativeZero := Float.ofBits 0x8000000000000000
  let tiny := Float.ofBits 1
  for h
      in [
        #[0.0, 0.0, 0.0, 0.0],
        #[0.015625, 0.0, 0.0, 0.015625],
        #[0.015625, -0.015625, 0.015625, 0.015625]
      ] do
    for k
        in [
          #[0.0, negativeZero, negativeZero, 0.0],
          #[0.3125, 0.3125, -0.3125, -0.3125],
          #[0.3125, -0.3125, 0.3125, 0.3125]
        ] do
      for mu
          in [
            #[0.0625, -0.0625],
            #[-0.0625, 0.0625],
            #[0.0, negativeZero],
            #[tiny, -tiny],
            #[0.28125, -0.28125],
            #[-0.28125, 0.28125]
          ] do
        for z in [#[1.0, -1.0], #[-1.0, 1.0], #[negativeZero, 0.0], #[tiny, -tiny]] do
          let projected ← requireOk (multiply 2 2 1 h mu) "mean projected product"
          let residual ← requireOk (sub z projected) "mean residual subtraction"
          let increment ← requireOk (multiply 2 2 1 k residual) "mean gain increment"
          let output ← requireOk (add mu increment) "mean final addition"
          for (a, cap)
              in [
                (projected, 0.015625),
                (residual, 1.03125),
                (increment, 0.703125),
                (output, 1.0)
              ] do
            check (a.size == 2 && a.all Float.isFinite && a.all (fun v => v.abs ≤ cap))
              "mean intermediate magnitude and finite storage"
          let r0 :=
            z.getD 0 0.0 - (entry 2 h 0 0 * mu.getD 0 0.0 + entry 2 h 0 1 * mu.getD 1 0.0)
          let r1 :=
            z.getD 1 0.0 - (entry 2 h 1 0 * mu.getD 0 0.0 + entry 2 h 1 1 * mu.getD 1 0.0)
          let reference :=
            #[
              mu.getD 0 0.0 + entry 2 k 0 0 * r0 + entry 2 k 0 1 * r1,
              mu.getD 1 0.0 + entry 2 k 1 0 * r0 + entry 2 k 1 1 * r1
            ]
          check (close output reference 2.842170943040401e-14)
            "mean stored-gain independent reference"

/-- Original process-noise endpoints/correlation and small nonzero transitions
derive prediction headroom in native execution. Independent scalar prediction
formulas include original Q. The result is then used in an actual correction. -/
def predictionInputDomainChecks : IO Unit := do
  let negativeZero := Float.ofBits 0x8000000000000000
  let h := #[0.015625, -0.015625, 0.015625, 0.015625]
  for q0 in [1.0, 1.5] do
    for q1 in [1.0, 1.5] do
      for qc in [-0.25, 0.0, 0.25] do
        let q := #[q0, qc, qc, q1]
        for l
            in [
              #[1.0, 0.0, 0.125, 1.0],
              #[1.25, negativeZero, -0.25, 1.25],
              #[0.5, 0.0, 0.25, 1.0]
            ] do
          for f
              in [
                #[0.0, 0.0, 0.0, 0.0],
                #[0.015625, 0.0, 0.0, 0.015625],
                #[0.015625, -0.015625, 0.015625, 0.015625],
                #[0.125, 0.0, 0.0, 0.125],
                #[0.125, -0.125, 0.125, 0.125],
                #[0.125, 0.125, 0.125, 0.125]
              ] do
            for mu in [#[1.0, -1.0], #[-1.0, 1.0], #[0.0, negativeZero]] do
              let input : Model := ⟨2, 2, f, h, q, identity 2, #[1.0, -1.0]⟩
              let predicted ←
                requireOk (SquareRootFilter.predictUnchecked input ⟨mu, l⟩)
                  "prediction local original-input execution"
              check (predicted.validate 2 matches .ok ())
                "prediction local output validation"
              check
                (predicted.mean.all (fun v => v.abs ≤ 0.28125)
                  && predicted.lower.all (fun v => v.abs ≤ 2.0))
                "prediction correction headroom"
              let p00 := entry 2 l 0 0 * entry 2 l 0 0
              let p01 := entry 2 l 0 0 * entry 2 l 1 0
              let p11 := entry 2 l 1 0 * entry 2 l 1 0 + entry 2 l 1 1 * entry 2 l 1 1
              let ref00 :=
                entry 2 f 0 0 * entry 2 f 0 0 * p00
                + 2.0 * entry 2 f 0 0 * entry 2 f 0 1 * p01
                + entry 2 f 0 1 * entry 2 f 0 1 * p11
                + q0
              let ref01 :=
                entry 2 f 0 0 * entry 2 f 1 0 * p00
                + (entry 2 f 0 0 * entry 2 f 1 1 + entry 2 f 0 1 * entry 2 f 1 0) * p01
                + entry 2 f 0 1 * entry 2 f 1 1 * p11
                + qc
              let ref11 :=
                entry 2 f 1 0 * entry 2 f 1 0 * p00
                + 2.0 * entry 2 f 1 0 * entry 2 f 1 1 * p01
                + entry 2 f 1 1 * entry 2 f 1 1 * p11
                + q1
              let dense ←
                requireOk (SquareRootFilter.materialize 2 predicted)
                  "prediction Gram regression"
              check (dense.covariance.all (fun v => v.abs ≤ 1.75))
                "prediction covariance entry enclosure"
              let d00 := entry 2 dense.covariance 0 0 - 2.0 / 3.0
              let d11 := entry 2 dense.covariance 1 1 - 2.0 / 3.0
              let d01 := entry 2 dense.covariance 0 1
              check (0.0 ≤ d00 && 0.0 ≤ d11 && 0.0 ≤ d00 * d11 - d01 * d01)
                "prediction covariance floor regression"
              check (close dense.covariance #[ref00, ref01, ref01, ref11] 1.0e-12)
                "prediction independent original-noise covariance reference"
              let meanRef :=
                #[
                  entry 2 f 0 0 * mu.getD 0 0.0 + entry 2 f 0 1 * mu.getD 1 0.0,
                  entry 2 f 1 0 * mu.getD 0 0.0 + entry 2 f 1 1 * mu.getD 1 0.0
                ]
              check (close predicted.mean meanRef 1.4210854715202004e-14)
                "prediction independent mean reference"
              let corrected ←
                requireOk (SquareRootFilter.updateUnchecked input predicted)
                  "prediction to local correction execution"
              check
                (corrected.mean.size == 2
                  && corrected.mean.all Float.isFinite
                  && corrected.mean.all (fun v => v.abs ≤ 1.0))
                "prediction to correction mean bound"
              check (corrected.validate 2 matches .ok ())
                "posterior returned factor validation"
              check (corrected.lower.all (fun v => v.abs ≤ 2.0)) "posterior factor bound"
              let posteriorDense ←
                requireOk (SquareRootFilter.materialize 2 corrected)
                  "posterior Gram regression"
              check (posteriorDense.covariance.all (fun v => v.abs ≤ 2.0))
                "posterior covariance bound for next prediction"
              let initialDense : State := ⟨mu, #[1.0, 0.25, 0.25, 1.5]⟩
              let inputs :=
                fun t =>
                  {
                    input with
                      measurement := if t % 2 == 0 then #[1.0, -1.0] else #[-1.0, 1.0]
                      processNoise := if t % 2 == 0 then q else #[q0, -qc, -qc, q1]
                      measurementNoise :=
                        if t % 2 == 0 then
                          #[1.0, 0.25, 0.25, 1.5]
                        else
                          #[1.5, -0.25, -0.25, 1.0]
                  }
              let retained ←
                requireOk (SquareRootFilter.fromCovariance (inputs 0) initialDense)
                  "original-input invariant initialization"
              let mut current := retained
              let mut reference := initialDense
              for t in [:4] do
                current ←
                  requireOk (SquareRootFilter.step (inputs t) current)
                    "original-input invariant checked step"
                reference ←
                  requireOk (CovarianceFilter.step .joseph (inputs t) reference)
                    "original-input invariant independent Joseph step"
                check (current.validate 2 matches .ok ()) "invariant factor validation"
                check
                  (current.mean.all (fun v => v.abs ≤ 1.0)
                    && current.lower.all (fun v => v.abs ≤ 2.0))
                  "invariant mean/factor caps"
                let represented ←
                  requireOk (SquareRootFilter.materialize 2 current)
                    "invariant represented covariance regression"
                check (represented.covariance.all (fun v => v.abs ≤ 2.0))
                  "invariant covariance cap"
                check
                  (close represented.covariance reference.covariance 1.0e-12
                    && close represented.mean reference.mean 1.0e-12)
                  "invariant independent full Joseph trajectory reference"
              let driven ←
                requireOk (SquareRootFilter.run inputs retained 4)
                  "original-input invariant trajectory driver"
              check
                (driven.lower.map Float.toBits == current.lower.map Float.toBits
                  && driven.mean.map Float.toBits == current.mean.map Float.toBits)
                "invariant driver agrees with repeated checked steps"

/-- Stored-gain endpoint cases test the posterior arithmetic and QR margins.
An independent scalar Joseph formula uses original R and the same stored gain.
The rounded dense Gram checks are regressions, not a universal positivity proof. -/
def posteriorInputDomainChecks : IO Unit := do
  let negativeZero := Float.ofBits 0x8000000000000000
  for r0 in [1.0, 1.5] do
    for r1 in [1.0, 1.5] do
      for rc in [-0.25, 0.0, 0.25] do
        let tr ←
          requireOk (cholesky 2 #[r0, rc, rc, r1]) "posterior original noise factor"
        for l
            in [
              #[1.0, 0.0, 0.125, 1.0],
              #[1.3125, negativeZero, -0.125, 1.3125],
              #[0.875, 0.0, 0.03125, 1.0]
            ] do
          for h
              in [
                #[0.0, 0.0, 0.0, 0.0],
                #[0.015625, 0.0, 0.0, 0.015625],
                #[0.015625, -0.015625, 0.015625, 0.015625]
              ] do
            for k
                in [
                  #[0.0, negativeZero, negativeZero, 0.0],
                  #[0.1640625, 0.0, 0.0, 0.1640625],
                  #[0.1640625, -0.1640625, 0.1640625, 0.1640625]
                ] do
              let kh ← requireOk (multiply 2 2 2 k h) "posterior KH product"
              let w ← requireOk (sub (identity 2) kh) "posterior identity subtraction"
              check (w.all (fun v => v.abs ≤ 1.03125)) "posterior W bound"
              let wl ← requireOk (multiply 2 2 2 w l) "posterior WL product"
              let ktr ← requireOk (multiply 2 2 2 k tr) "posterior KTR product"
              let a := fromCols 2 2 2 wl ktr
              let gram ←
                requireOk (multiply 2 4 2 a (transpose 2 4 a)) "posterior prearray Gram"
              check ((entry 2 gram 0 0 ≤ 1.96875) && (entry 2 gram 1 1 ≤ 1.96875))
                "posterior prearray energy headroom"
              let d0 := entry 2 gram 0 0 - 0.5
              let d1 := entry 2 gram 1 1 - 0.5
              let c := entry 2 gram 0 1
              check (0.0 ≤ d0 && 0.0 ≤ d1 && 0.0 ≤ d0 * d1 - c * c)
                "posterior prearray rank margin regression"
              let lower ←
                requireOk (OrthogonalFactorization.gramFactor 2 4 a) "posterior QR"
              let output : FactorState := ⟨#[0.0, 0.0], lower⟩
              check (output.validate 2 matches .ok ()) "posterior QR factor validation"
              check (lower.all (fun v => v.abs ≤ 2.0)) "posterior QR factor cap"
              let dense ←
                requireOk (SquareRootFilter.materialize 2 output) "posterior output Gram"
              check (dense.covariance.all (fun v => v.abs ≤ 2.0))
                "posterior QR covariance cap"
              let p00 := entry 2 l 0 0 * entry 2 l 0 0
              let p01 := entry 2 l 0 0 * entry 2 l 1 0
              let p11 := entry 2 l 1 0 * entry 2 l 1 0 + entry 2 l 1 1 * entry 2 l 1 1
              let w00 :=
                1.0 - (entry 2 k 0 0 * entry 2 h 0 0 + entry 2 k 0 1 * entry 2 h 1 0)
              let w01 := -(entry 2 k 0 0 * entry 2 h 0 1 + entry 2 k 0 1 * entry 2 h 1 1)
              let w10 := -(entry 2 k 1 0 * entry 2 h 0 0 + entry 2 k 1 1 * entry 2 h 1 0)
              let w11 :=
                1.0 - (entry 2 k 1 0 * entry 2 h 0 1 + entry 2 k 1 1 * entry 2 h 1 1)
              let ref00 :=
                w00 * w00 * p00
                + 2.0 * w00 * w01 * p01
                + w01 * w01 * p11
                + entry 2 k 0 0 * entry 2 k 0 0 * r0
                + 2.0 * entry 2 k 0 0 * entry 2 k 0 1 * rc
                + entry 2 k 0 1 * entry 2 k 0 1 * r1
              let ref01 :=
                w00 * w10 * p00
                + (w00 * w11 + w01 * w10) * p01
                + w01 * w11 * p11
                + entry 2 k 0 0 * entry 2 k 1 0 * r0
                + (entry 2 k 0 0 * entry 2 k 1 1 + entry 2 k 0 1 * entry 2 k 1 0) * rc
                + entry 2 k 0 1 * entry 2 k 1 1 * r1
              let ref11 :=
                w10 * w10 * p00
                + 2.0 * w10 * w11 * p01
                + w11 * w11 * p11
                + entry 2 k 1 0 * entry 2 k 1 0 * r0
                + 2.0 * entry 2 k 1 0 * entry 2 k 1 1 * rc
                + entry 2 k 1 1 * entry 2 k 1 1 * r1
              check (close dense.covariance #[ref00, ref01, ref01, ref11] 1.0e-12)
                "posterior independent original-noise Joseph reference"

/-- Retention itself has no norm/domain cap. These references are independent
analytic signed copies; dense Gram checks here use small exactly representable integers. -/
def qrRetentionChecks : IO Unit := do
  let r := #[-2.0, 3.0, -4.0, 91.0, 5.0, -6.0, 92.0, 93.0, -7.0, 94.0, 95.0, 96.0]
  let l ← requireOk (OrthogonalFactorization.retainFactor 3 r) "QR signed retention"
  check (close l #[2.0, 0.0, 0.0, -3.0, 5.0, 0.0, 4.0, -6.0, 7.0] 0.0)
    "QR analytic signed transpose"
  for i in [:3] do
    check (0.0 < entry 3 l i i) "QR retained diagonal positivity"
    for j in [i + 1:3] do
      check ((entry 3 l i j).toBits == 0) "QR retained upper triangle positive zeros"
  let gram ← requireOk (multiply 3 3 3 l (transpose 3 3 l)) "QR retained small Gram"
  check (close gram #[4.0, -6.0, 8.0, -6.0, 34.0, -42.0, 8.0, -42.0, 101.0] 0.0)
    "QR retained upper-block Gram reference"
  let tiny := Float.ofBits 0x0000000000000001
  let huge := Float.ofBits 0x7fefffffffffffff
  let negativeZero := Float.ofBits 0x8000000000000000
  for x in [tiny, huge] do
    for sign in [1.0, -1.0] do
      let signedBits := if sign < 0.0 then x.toBits ^^^ 0x8000000000000000 else x.toBits
      let diagonal ←
        requireOk (OrthogonalFactorization.retainFactor 1 #[Float.ofBits signedBits])
          "QR full-range diagonal retention"
      check ((diagonal.getD 0 0.0).toBits == x.toBits)
        "QR full-range exact absolute diagonal"
      let edges ←
        requireOk (OrthogonalFactorization.retainFactor 2 #[sign, x, 0.0, x])
          "QR full-range off-diagonal retention"
      check ((entry 2 edges 1 0).toBits == signedBits) "QR full-range sign multiplication"
  for zero in [0.0, negativeZero] do
    check
      (OrthogonalFactorization.retainFactor 1 #[zero] matches .error .nonpositivePivot)
      "QR retention rejects both zero diagonals"
    for sign in [1.0, -1.0] do
      let zeros ←
        requireOk (OrthogonalFactorization.retainFactor 2 #[sign, zero, 0.0, 1.0])
          "QR signed-zero off-diagonal retention"
      let expectedBits :=
        if sign < 0.0 then zero.toBits ^^^ 0x8000000000000000 else zero.toBits
      check ((entry 2 zeros 1 0).toBits == expectedBits) "QR signed-zero copy bits"
  let empty ← requireOk (OrthogonalFactorization.retainFactor 0 #[]) "QR empty retention"
  check (empty.isEmpty) "QR empty retained shape"
  let large ←
    requireOk (OrthogonalFactorization.retainFactor 33 (identity 33))
      "QR retention beyond local norm dimension cap"
  check (close large (identity 33) 0.0) "QR 33-dimensional exact retained identity"
  let copied ←
    requireOk
      (OrthogonalFactorization.copyFactorColumn 2 0 [1, 1]
        #[-1.0, 3.0, 0.0, 2.0] #[7.0, 8.0, 9.0, 10.0])
      "QR duplicate retained write"
  check (close copied #[7.0, 8.0, -3.0, 10.0] 0.0)
    "QR duplicate copy and untouched entries"
  check
    (OrthogonalFactorization.retainFactor 2 #[1.0, Float.nan, 0.0, 1.0]
      matches .error .nonfiniteComputation)
    "QR exceptional retained product"
  check
    (OrthogonalFactorization.retainFactor 1 #[Float.inf]
      matches .error .nonfiniteComputation)
    "QR infinite retained diagonal"
  check
    (OrthogonalFactorization.retainFactor 1 #[Float.nan] matches .error .nonpositivePivot)
    "QR NaN diagonal guard order"
  check (OrthogonalFactorization.retainFactor 1 #[] matches .error .nonpositivePivot)
    "QR default-zero missing diagonal"

/-- P=H=1, R=2⁻⁵⁴: conventional posterior is zero; the real value is positive. -/
def cancellationChecks : IO Unit := do
  let r := Float.ofBits 0x3c90000000000000
  let input := scalar 1.0 r 1.0
  let initial : State := ⟨#[0.0], #[1.0]⟩
  for form in [CovarianceFilter.Form.compact, .subtractive] do
    let result ←
      requireOk (CovarianceFilter.update form input initial) "cancellation conventional"
    check (result.covariance.getD 0 1.0 == 0.0)
      "expected zero covariance from cancellation"
  let stabilized ←
    requireOk (CovarianceFilter.update .joseph input initial) "cancellation Joseph"
  check (stabilized.covariance.getD 0 0.0 == r) "Joseph scalar cancellation regression"
  let factor ←
    requireOk (SquareRootFilter.fromCovariance input initial)
      "cancellation initialization"
  let result ← requireOk (SquareRootFilter.update input factor) "cancellation square root"
  check (0.0 < result.lower.getD 0 0.0) "square-root scalar cancellation lost rank"

/-- Boundary/interior diagonal LDLᵀ solves, dense signed RHS values, and
both zero signs. Check the original-system residual and exact decoded zero
preservation separately from the formal forward-error theorem. -/
def josephDiagonalSolveChecks : IO Unit := do
  for a0 in [1.5, 2.0, 3.25, 5.0] do
    for a1 in [1.5, 2.0, 3.25, 5.0] do
      for zero in [0.0, -0.0] do
        let a := #[a0, zero, zero, a1]
        for b
            in [
              #[4.0, -4.0, 1.0 / 3.0, -1.5],
              #[-4.0, 2.5, -2.5, 4.0],
              #[4.0, zero, zero, -4.0]
            ] do
          let x ← requireOk (solveSPD 2 2 a b) "Joseph diagonal LDL solve"
          check (x.size == 4 && x.all Float.isFinite) "Joseph LDL finite output"
          for i in [:2] do
            for j in [:2] do
              let residual :=
                a.getD (i * 2 + i) 0.0 * x.getD (i * 2 + j) 0.0 - b.getD (i * 2 + j) 0.0
              check (residual.abs ≤ 1.0e-13) "Joseph LDL original-system residual"
          if b.getD 1 0.0 == 0.0 && b.getD 2 0.0 == 0.0 then
            check (x.getD 1 1.0 == 0.0 && x.getD 2 1.0 == 0.0)
              "Joseph LDL decoded diagonal preservation"

/-- Local Joseph positivity with fully observed diagonal inputs, including
nonoptimal signed gains and both signed-zero words. This checks the rounded
dense result itself, not a retained factor or an exact Gram interpretation. -/
def josephDiagonalPositiveChecks : IO Unit := do
  for p
      in [
        #[0.5, 0.0, 0.0, 0.5],
        #[0.5, -0.0, -0.0, 2.0],
        #[2.0, 0.0, 0.0, 0.5],
        #[2.0, -0.0, -0.0, 2.0],
        #[0.5, -0.0, -0.0, 4.0],
        #[4.0, 0.0, 0.0, 4.0]
      ] do
    for r in [#[0.5, 0.0, 0.0, 0.5], #[1.0, -0.0, -0.0, 1.5], #[1.5, 0.0, 0.0, 0.5]] do
      for k
          in [
            #[-1.0, 0.0, -0.0, -1.0 / 3.0],
            #[0.0, -0.0, 0.0, 1.0],
            #[1.0 / 3.0, -0.0, -0.0, 0.5],
            #[1.0, 0.0, 0.0, -1.0]
          ] do
        let input : Model := ⟨2, 2, identity 2, identity 2, identity 2, r, #[0.0, 0.0]⟩
        let prior : State := ⟨#[0.0, 0.0], p⟩
        let out ←
          requireOk (CovarianceFilter.covarianceUnchecked .joseph input prior k)
            "diagonal Joseph covariance kernel"
        check (out.size == 4 && out.all Float.isFinite) "diagonal Joseph finite output"
        check (out.getD 1 1.0 == 0.0 && out.getD 2 1.0 == 0.0)
          "diagonal Joseph exact off-diagonal zeros"
        check (out.getD 0 0.0 ≥ 0.125 && out.getD 3 0.0 ≥ 0.125)
          "diagonal Joseph retained positive floor"

/-- Independent exact-rational expanded-polynomial references, generated by
JosephReference.py. Includes correlated priors/noise, signed gains, non-dyadic
gain words, signed zeros and a subnormal gain. This tests the covariance kernel
at supplied gains, separately from full-filter accuracy. -/
def josephStoredInputChecks : IO Unit := do
  let references : Array (Array Float) :=
    #[
      #[1, 0.25, 0.25, 1.5],
      #[1.1666666666666667, 0.27777777777777779, 0.27777777777777779, 1.6111111111111112],
      #[1.3333333333333333, 0.30555555555555552, 0.30555555555555552, 1.7222222222222221],
      #[1, 0.25, 0.25, 1.515625],
      #[4, 0.75, 0.75, 3.5],
      #[1, 0.25, 0.25, 1.5],
      #[1.1562771267361112, 0.2751803927951389, 0.2751803927951389, 1.5955268012152777],
      #[1.3203938802083333, 0.29252115885416669, 0.29252115885416669, 1.7352973090277777],
      #[1, 0.25048828125, 0.25048828125, 1.5214900970458984],
      #[3.961669921875, 0.7108154296875, 0.7108154296875, 3.53955078125],
      #[1, 0.25, 0.25, 1.5],
      #[1.1589084201388888, 0.29081217447916669, 0.29081217447916669, 1.6294216579861112],
      #[1.3387044270833333, 0.31073676215277779, 0.31073676215277779, 1.7171223958333333],
      #[1, 0.24755859375, 0.24755859375, 1.5088005065917969],
      #[4.01708984375, 0.765380859375, 0.765380859375, 3.4853515625],
      #[1, 0.25, 0.25, 1.5],
      #[0.61111111111111116, 0.25, 0.25, 2.7777777777777777],
      #[1.0555555555555556, 0.25, 0.25, 0.88888888888888884],
      #[1, 0.21875, 0.21875, 1.1640625],
      #[4.5, 0.25, 0.25, 3],
      #[2, 0.25, 0.25, 1.5],
      #[2.1666666666666665, 0.27777777777777779, 0.27777777777777779, 1.6111111111111112],
      #[2.3333333333333335, 0.30555555555555552, 0.30555555555555552, 1.7222222222222221],
      #[2, 0.25, 0.25, 1.515625],
      #[5, 0.75, 0.75, 3.5],
      #[2, 0.25, 0.25, 1.5],
      #[2.1458875868055554, 0.2751803927951389, 0.2751803927951389, 1.5955268012152777],
      #[2.3100043402777777, 0.28733995225694442, 0.28733995225694442, 1.7353244357638888],
      #[2, 0.25048828125, 0.25048828125, 1.5214900970458984],
      #[4.9306640625, 0.6954345703125, 0.6954345703125, 3.539794921875],
      #[2, 0.25, 0.25, 1.5],
      #[2.1485188802083335, 0.2959933810763889, 0.2959933810763889, 1.6294487847222221],
      #[2.3387044270833335, 0.3003200954861111, 0.3003200954861111, 1.7172309027777777],
      #[2, 0.24560546875, 0.24560546875, 1.5088043212890625],
      #[5.01708984375, 0.734130859375, 0.734130859375, 3.486328125],
      #[2, 0.25, 0.25, 1.5],
      #[1.0555555555555556, 0.25, 0.25, 2.7777777777777777],
      #[1.5, 0.027777777777777783, 0.027777777777777783, 1],
      #[2, 0.21875, 0.21875, 1.1640625],
      #[4.5, 0.25, 0.25, 4],
      #[4, 0.25, 0.25, 1.5],
      #[4.166666666666667, 0.27777777777777779, 0.27777777777777779, 1.6111111111111112],
      #[4.333333333333333, 0.30555555555555552, 0.30555555555555552, 1.7222222222222221],
      #[4, 0.25, 0.25, 1.515625],
      #[7, 0.75, 0.75, 3.5],
      #[4, 0.25, 0.25, 1.5],
      #[4.1251085069444446, 0.2751803927951389, 0.2751803927951389, 1.5955268012152777],
      #[4.289225260416667, 0.2769775390625, 0.2769775390625, 1.7353786892361112],
      #[4, 0.25048828125, 0.25048828125, 1.5214900970458984],
      #[6.86865234375, 0.6646728515625, 0.6646728515625, 3.540283203125],
      #[4, 0.25, 0.25, 1.5],
      #[4.1277398003472223, 0.30635579427083331, 0.30635579427083331, 1.6295030381944444],
      #[4.338704427083333, 0.27948676215277779, 0.27948676215277779, 1.7174479166666667],
      #[4, 0.24169921875, 0.24169921875, 1.5088119506835938],
      #[7.01708984375, 0.671630859375, 0.671630859375, 3.48828125],
      #[4, 0.25, 0.25, 1.5],
      #[1.9444444444444444, 0.25, 0.25, 2.7777777777777777],
      #[
        2.3888888888888888,
        -0.41666666666666663,
        -0.41666666666666663,
        1.2222222222222221
      ],
      #[4, 0.21875, 0.21875, 1.1640625],
      #[4.5, 0.25, 0.25, 6]
    ]
  let gains : Array (Array Float) :=
    #[
      #[0.0, -0.0, 0.0, 0.0],
      #[1.0 / 3.0, 0.0, 0.0, -1.0 / 3.0],
      #[1.0 / 3.0, -1.0 / 3.0, 1.0 / 3.0, 1.0 / 3.0],
      #[Float.ofBits 1, 0.0, -0.0, 0.125],
      #[1.0, -1.0, 1.0, 1.0]
    ]
  let observations : Array (Array Float) :=
    #[
      #[0.0, -0.0, 0.0, 0.0],
      #[0.015625, 0.0, -0.0, -0.015625],
      #[0.015625, -0.015625, 0.015625, 0.015625],
      identity 2
    ]
  let mut index := 0
  for p0 in #[1.0, 2.0, 4.0] do
    let prior : State := ⟨#[0.0, 0.0], #[p0, 0.25, 0.25, 1.5]⟩
    for h in observations do
      let input : Model :=
        ⟨2, 2, identity 2, h, identity 2, #[1.5, -0.25, -0.25, 1.0], #[0.0, 0.0]⟩
      for k in gains do
        let output ←
          requireOk (CovarianceFilter.covarianceUnchecked .joseph input prior k)
            "stored-input Joseph covariance"
        check (output.size == 4 && output.all Float.isFinite) "Joseph finite output shape"
        check (close output (references.getD index #[]) 1.0e-14)
          "Joseph exact-rational expanded polynomial reference"
        index := index + 1
  check (index == references.size) "Joseph oracle coverage"

/-- Full native correction gain against exact-rational original-input ratios.
Boundary/interior variances include non-dyadic words and both signed zeros.
The oracle does not round the innovation before evaluating the reference. -/
def josephComputedGainChecks : IO Unit := do
  let references : Array (Array Float) :=
    #[
      #[0.4838709677419355, 0, 0, 0.4838709677419355],
      #[0.4838709677419355, 0, 0, 0.41284403669724773],
      #[0.4838709677419355, 0, 0, 0.38461538461538464],
      #[0.41284403669724773, 0, 0, 0.4838709677419355],
      #[0.41284403669724773, 0, 0, 0.41284403669724773],
      #[0.41284403669724773, 0, 0, 0.38461538461538464],
      #[0.38461538461538464, 0, 0, 0.4838709677419355],
      #[0.38461538461538464, 0, 0, 0.41284403669724773],
      #[0.38461538461538464, 0, 0, 0.38461538461538464],
      #[0.4838709677419355, 0, 0, 0.5714285714285714],
      #[0.4838709677419355, 0, 0, 0.5],
      #[0.4838709677419355, 0, 0, 0.47058823529411764],
      #[0.41284403669724773, 0, 0, 0.5714285714285714],
      #[0.41284403669724773, 0, 0, 0.5],
      #[0.41284403669724773, 0, 0, 0.47058823529411764],
      #[0.38461538461538464, 0, 0, 0.5714285714285714],
      #[0.38461538461538464, 0, 0, 0.5],
      #[0.38461538461538464, 0, 0, 0.47058823529411764],
      #[0.4838709677419355, 0, 0, 0.66666666666666663],
      #[0.4838709677419355, 0, 0, 0.59999999999999998],
      #[0.4838709677419355, 0, 0, 0.5714285714285714],
      #[0.41284403669724773, 0, 0, 0.66666666666666663],
      #[0.41284403669724773, 0, 0, 0.59999999999999998],
      #[0.41284403669724773, 0, 0, 0.5714285714285714],
      #[0.38461538461538464, 0, 0, 0.66666666666666663],
      #[0.38461538461538464, 0, 0, 0.59999999999999998],
      #[0.38461538461538464, 0, 0, 0.5714285714285714],
      #[0.4838709677419355, 0, 0, 0.76470588235294112],
      #[0.4838709677419355, 0, 0, 0.70909090909090911],
      #[0.4838709677419355, 0, 0, 0.68421052631578949],
      #[0.41284403669724773, 0, 0, 0.76470588235294112],
      #[0.41284403669724773, 0, 0, 0.70909090909090911],
      #[0.41284403669724773, 0, 0, 0.68421052631578949],
      #[0.38461538461538464, 0, 0, 0.76470588235294112],
      #[0.38461538461538464, 0, 0, 0.70909090909090911],
      #[0.38461538461538464, 0, 0, 0.68421052631578949],
      #[0.5714285714285714, 0, 0, 0.4838709677419355],
      #[0.5714285714285714, 0, 0, 0.41284403669724773],
      #[0.5714285714285714, 0, 0, 0.38461538461538464],
      #[0.5, 0, 0, 0.4838709677419355],
      #[0.5, 0, 0, 0.41284403669724773],
      #[0.5, 0, 0, 0.38461538461538464],
      #[0.47058823529411764, 0, 0, 0.4838709677419355],
      #[0.47058823529411764, 0, 0, 0.41284403669724773],
      #[0.47058823529411764, 0, 0, 0.38461538461538464],
      #[0.5714285714285714, 0, 0, 0.5714285714285714],
      #[0.5714285714285714, 0, 0, 0.5],
      #[0.5714285714285714, 0, 0, 0.47058823529411764],
      #[0.5, 0, 0, 0.5714285714285714],
      #[0.5, 0, 0, 0.5],
      #[0.5, 0, 0, 0.47058823529411764],
      #[0.47058823529411764, 0, 0, 0.5714285714285714],
      #[0.47058823529411764, 0, 0, 0.5],
      #[0.47058823529411764, 0, 0, 0.47058823529411764],
      #[0.5714285714285714, 0, 0, 0.66666666666666663],
      #[0.5714285714285714, 0, 0, 0.59999999999999998],
      #[0.5714285714285714, 0, 0, 0.5714285714285714],
      #[0.5, 0, 0, 0.66666666666666663],
      #[0.5, 0, 0, 0.59999999999999998],
      #[0.5, 0, 0, 0.5714285714285714],
      #[0.47058823529411764, 0, 0, 0.66666666666666663],
      #[0.47058823529411764, 0, 0, 0.59999999999999998],
      #[0.47058823529411764, 0, 0, 0.5714285714285714],
      #[0.5714285714285714, 0, 0, 0.76470588235294112],
      #[0.5714285714285714, 0, 0, 0.70909090909090911],
      #[0.5714285714285714, 0, 0, 0.68421052631578949],
      #[0.5, 0, 0, 0.76470588235294112],
      #[0.5, 0, 0, 0.70909090909090911],
      #[0.5, 0, 0, 0.68421052631578949],
      #[0.47058823529411764, 0, 0, 0.76470588235294112],
      #[0.47058823529411764, 0, 0, 0.70909090909090911],
      #[0.47058823529411764, 0, 0, 0.68421052631578949],
      #[0.66666666666666663, 0, 0, 0.4838709677419355],
      #[0.66666666666666663, 0, 0, 0.41284403669724773],
      #[0.66666666666666663, 0, 0, 0.38461538461538464],
      #[0.59999999999999998, 0, 0, 0.4838709677419355],
      #[0.59999999999999998, 0, 0, 0.41284403669724773],
      #[0.59999999999999998, 0, 0, 0.38461538461538464],
      #[0.5714285714285714, 0, 0, 0.4838709677419355],
      #[0.5714285714285714, 0, 0, 0.41284403669724773],
      #[0.5714285714285714, 0, 0, 0.38461538461538464],
      #[0.66666666666666663, 0, 0, 0.5714285714285714],
      #[0.66666666666666663, 0, 0, 0.5],
      #[0.66666666666666663, 0, 0, 0.47058823529411764],
      #[0.59999999999999998, 0, 0, 0.5714285714285714],
      #[0.59999999999999998, 0, 0, 0.5],
      #[0.59999999999999998, 0, 0, 0.47058823529411764],
      #[0.5714285714285714, 0, 0, 0.5714285714285714],
      #[0.5714285714285714, 0, 0, 0.5],
      #[0.5714285714285714, 0, 0, 0.47058823529411764],
      #[0.66666666666666663, 0, 0, 0.66666666666666663],
      #[0.66666666666666663, 0, 0, 0.59999999999999998],
      #[0.66666666666666663, 0, 0, 0.5714285714285714],
      #[0.59999999999999998, 0, 0, 0.66666666666666663],
      #[0.59999999999999998, 0, 0, 0.59999999999999998],
      #[0.59999999999999998, 0, 0, 0.5714285714285714],
      #[0.5714285714285714, 0, 0, 0.66666666666666663],
      #[0.5714285714285714, 0, 0, 0.59999999999999998],
      #[0.5714285714285714, 0, 0, 0.5714285714285714],
      #[0.66666666666666663, 0, 0, 0.76470588235294112],
      #[0.66666666666666663, 0, 0, 0.70909090909090911],
      #[0.66666666666666663, 0, 0, 0.68421052631578949],
      #[0.59999999999999998, 0, 0, 0.76470588235294112],
      #[0.59999999999999998, 0, 0, 0.70909090909090911],
      #[0.59999999999999998, 0, 0, 0.68421052631578949],
      #[0.5714285714285714, 0, 0, 0.76470588235294112],
      #[0.5714285714285714, 0, 0, 0.70909090909090911],
      #[0.5714285714285714, 0, 0, 0.68421052631578949],
      #[0.76470588235294112, 0, 0, 0.4838709677419355],
      #[0.76470588235294112, 0, 0, 0.41284403669724773],
      #[0.76470588235294112, 0, 0, 0.38461538461538464],
      #[0.70909090909090911, 0, 0, 0.4838709677419355],
      #[0.70909090909090911, 0, 0, 0.41284403669724773],
      #[0.70909090909090911, 0, 0, 0.38461538461538464],
      #[0.68421052631578949, 0, 0, 0.4838709677419355],
      #[0.68421052631578949, 0, 0, 0.41284403669724773],
      #[0.68421052631578949, 0, 0, 0.38461538461538464],
      #[0.76470588235294112, 0, 0, 0.5714285714285714],
      #[0.76470588235294112, 0, 0, 0.5],
      #[0.76470588235294112, 0, 0, 0.47058823529411764],
      #[0.70909090909090911, 0, 0, 0.5714285714285714],
      #[0.70909090909090911, 0, 0, 0.5],
      #[0.70909090909090911, 0, 0, 0.47058823529411764],
      #[0.68421052631578949, 0, 0, 0.5714285714285714],
      #[0.68421052631578949, 0, 0, 0.5],
      #[0.68421052631578949, 0, 0, 0.47058823529411764],
      #[0.76470588235294112, 0, 0, 0.66666666666666663],
      #[0.76470588235294112, 0, 0, 0.59999999999999998],
      #[0.76470588235294112, 0, 0, 0.5714285714285714],
      #[0.70909090909090911, 0, 0, 0.66666666666666663],
      #[0.70909090909090911, 0, 0, 0.59999999999999998],
      #[0.70909090909090911, 0, 0, 0.5714285714285714],
      #[0.68421052631578949, 0, 0, 0.66666666666666663],
      #[0.68421052631578949, 0, 0, 0.59999999999999998],
      #[0.68421052631578949, 0, 0, 0.5714285714285714],
      #[0.76470588235294112, 0, 0, 0.76470588235294112],
      #[0.76470588235294112, 0, 0, 0.70909090909090911],
      #[0.76470588235294112, 0, 0, 0.68421052631578949],
      #[0.70909090909090911, 0, 0, 0.76470588235294112],
      #[0.70909090909090911, 0, 0, 0.70909090909090911],
      #[0.70909090909090911, 0, 0, 0.68421052631578949],
      #[0.68421052631578949, 0, 0, 0.76470588235294112],
      #[0.68421052631578949, 0, 0, 0.70909090909090911],
      #[0.68421052631578949, 0, 0, 0.68421052631578949]
    ]
  let mut index := 0
  for p0 in [15.0 / 16.0, 4.0 / 3.0, 2.0, 13.0 / 4.0] do
    for p1 in [15.0 / 16.0, 4.0 / 3.0, 2.0, 13.0 / 4.0] do
      for r0 in [1.0, 4.0 / 3.0, 1.5] do
        for r1 in [1.0, 4.0 / 3.0, 1.5] do
          for zero in [0.0, -0.0] do
            let input : Model :=
              ⟨
                2,
                2,
                identity 2,
                #[1.0, zero, zero, 1.0],
                identity 2,
                #[r0, zero, zero, r1],
                #[0.0, 0.0]
              ⟩
            let prior : State := ⟨#[0.0, 0.0], #[p0, zero, zero, p1]⟩
            let c ←
              requireOk (CovarianceFilter.correctionUnchecked input prior)
                "Joseph original-input gain"
            check (c.gain.size == 4 && c.gain.all Float.isFinite) "Joseph finite gain"
            check (close c.gain (references.getD index #[]) 1.0e-14)
              "Joseph gain exact-rational original-input reference"
            check (c.gain.getD 1 1.0 == 0.0 && c.gain.getD 2 1.0 == 0.0)
              "Joseph computed gain diagonal"
            for i in [:2] do
              check
                (0.375 ≤ c.gain.getD (i * 2 + i) 0.0
                  && c.gain.getD (i * 2 + i) 0.0 ≤ 0.8125)
                "Joseph gain interval"
          index := index + 1
  check (index == references.size) "Joseph gain oracle coverage"

/-- Checked complete Joseph corrections at the reached prior/vector boundaries,
compared with exact-rational optimal updates of the original stored inputs. -/
def josephCompleteUpdateChecks : IO Unit := do
  let references : Array (Array Float) :=
    #[
      #[
        -1.096774193548387,
        1.096774193548387,
        0.4838709677419355,
        0,
        0,
        0.4838709677419355
      ],
      #[
        -0.12903225806451613,
        0.12903225806451613,
        0.4838709677419355,
        0,
        0,
        0.4838709677419355
      ],
      #[
        0.12903225806451613,
        -0.12903225806451613,
        0.4838709677419355,
        0,
        0,
        0.4838709677419355
      ],
      #[
        1.096774193548387,
        -1.096774193548387,
        0.4838709677419355,
        0,
        0,
        0.4838709677419355
      ],
      #[
        -1.096774193548387,
        1.1153846153846154,
        0.4838709677419355,
        0,
        0,
        0.57692307692307687
      ],
      #[
        -0.12903225806451613,
        0.34615384615384615,
        0.4838709677419355,
        0,
        0,
        0.57692307692307687
      ],
      #[
        0.12903225806451613,
        -0.34615384615384615,
        0.4838709677419355,
        0,
        0,
        0.57692307692307687
      ],
      #[
        1.096774193548387,
        -1.1153846153846154,
        0.4838709677419355,
        0,
        0,
        0.57692307692307687
      ],
      #[
        -1.1153846153846154,
        1.096774193548387,
        0.57692307692307687,
        0,
        0,
        0.4838709677419355
      ],
      #[
        -0.34615384615384615,
        0.12903225806451613,
        0.57692307692307687,
        0,
        0,
        0.4838709677419355
      ],
      #[
        0.34615384615384615,
        -0.12903225806451613,
        0.57692307692307687,
        0,
        0,
        0.4838709677419355
      ],
      #[
        1.1153846153846154,
        -1.096774193548387,
        0.57692307692307687,
        0,
        0,
        0.4838709677419355
      ],
      #[
        -1.1153846153846154,
        1.1153846153846154,
        0.57692307692307687,
        0,
        0,
        0.57692307692307687
      ],
      #[
        -0.34615384615384615,
        0.34615384615384615,
        0.57692307692307687,
        0,
        0,
        0.57692307692307687
      ],
      #[
        0.34615384615384615,
        -0.34615384615384615,
        0.57692307692307687,
        0,
        0,
        0.57692307692307687
      ],
      #[
        1.1153846153846154,
        -1.1153846153846154,
        0.57692307692307687,
        0,
        0,
        0.57692307692307687
      ],
      #[
        -1.096774193548387,
        1.0441176470588236,
        0.4838709677419355,
        0,
        0,
        0.76470588235294112
      ],
      #[
        -0.12903225806451613,
        -0.48529411764705882,
        0.4838709677419355,
        0,
        0,
        0.76470588235294112
      ],
      #[
        0.12903225806451613,
        0.48529411764705882,
        0.4838709677419355,
        0,
        0,
        0.76470588235294112
      ],
      #[
        1.096774193548387,
        -1.0441176470588236,
        0.4838709677419355,
        0,
        0,
        0.76470588235294112
      ],
      #[
        -1.096774193548387,
        1.0592105263157894,
        0.4838709677419355,
        0,
        0,
        1.0263157894736843
      ],
      #[
        -0.12903225806451613,
        -0.30921052631578949,
        0.4838709677419355,
        0,
        0,
        1.0263157894736843
      ],
      #[
        0.12903225806451613,
        0.30921052631578949,
        0.4838709677419355,
        0,
        0,
        1.0263157894736843
      ],
      #[
        1.096774193548387,
        -1.0592105263157894,
        0.4838709677419355,
        0,
        0,
        1.0263157894736843
      ],
      #[
        -1.1153846153846154,
        1.0441176470588236,
        0.57692307692307687,
        0,
        0,
        0.76470588235294112
      ],
      #[
        -0.34615384615384615,
        -0.48529411764705882,
        0.57692307692307687,
        0,
        0,
        0.76470588235294112
      ],
      #[
        0.34615384615384615,
        0.48529411764705882,
        0.57692307692307687,
        0,
        0,
        0.76470588235294112
      ],
      #[
        1.1153846153846154,
        -1.0441176470588236,
        0.57692307692307687,
        0,
        0,
        0.76470588235294112
      ],
      #[
        -1.1153846153846154,
        1.0592105263157894,
        0.57692307692307687,
        0,
        0,
        1.0263157894736843
      ],
      #[
        -0.34615384615384615,
        -0.30921052631578949,
        0.57692307692307687,
        0,
        0,
        1.0263157894736843
      ],
      #[
        0.34615384615384615,
        0.30921052631578949,
        0.57692307692307687,
        0,
        0,
        1.0263157894736843
      ],
      #[
        1.1153846153846154,
        -1.0592105263157894,
        0.57692307692307687,
        0,
        0,
        1.0263157894736843
      ],
      #[
        -1.0441176470588236,
        1.096774193548387,
        0.76470588235294112,
        0,
        0,
        0.4838709677419355
      ],
      #[
        0.48529411764705882,
        0.12903225806451613,
        0.76470588235294112,
        0,
        0,
        0.4838709677419355
      ],
      #[
        -0.48529411764705882,
        -0.12903225806451613,
        0.76470588235294112,
        0,
        0,
        0.4838709677419355
      ],
      #[
        1.0441176470588236,
        -1.096774193548387,
        0.76470588235294112,
        0,
        0,
        0.4838709677419355
      ],
      #[
        -1.0441176470588236,
        1.1153846153846154,
        0.76470588235294112,
        0,
        0,
        0.57692307692307687
      ],
      #[
        0.48529411764705882,
        0.34615384615384615,
        0.76470588235294112,
        0,
        0,
        0.57692307692307687
      ],
      #[
        -0.48529411764705882,
        -0.34615384615384615,
        0.76470588235294112,
        0,
        0,
        0.57692307692307687
      ],
      #[
        1.0441176470588236,
        -1.1153846153846154,
        0.76470588235294112,
        0,
        0,
        0.57692307692307687
      ],
      #[
        -1.0592105263157894,
        1.096774193548387,
        1.0263157894736843,
        0,
        0,
        0.4838709677419355
      ],
      #[
        0.30921052631578949,
        0.12903225806451613,
        1.0263157894736843,
        0,
        0,
        0.4838709677419355
      ],
      #[
        -0.30921052631578949,
        -0.12903225806451613,
        1.0263157894736843,
        0,
        0,
        0.4838709677419355
      ],
      #[
        1.0592105263157894,
        -1.096774193548387,
        1.0263157894736843,
        0,
        0,
        0.4838709677419355
      ],
      #[
        -1.0592105263157894,
        1.1153846153846154,
        1.0263157894736843,
        0,
        0,
        0.57692307692307687
      ],
      #[
        0.30921052631578949,
        0.34615384615384615,
        1.0263157894736843,
        0,
        0,
        0.57692307692307687
      ],
      #[
        -0.30921052631578949,
        -0.34615384615384615,
        1.0263157894736843,
        0,
        0,
        0.57692307692307687
      ],
      #[
        1.0592105263157894,
        -1.1153846153846154,
        1.0263157894736843,
        0,
        0,
        0.57692307692307687
      ],
      #[
        -1.0441176470588236,
        1.0441176470588236,
        0.76470588235294112,
        0,
        0,
        0.76470588235294112
      ],
      #[
        0.48529411764705882,
        -0.48529411764705882,
        0.76470588235294112,
        0,
        0,
        0.76470588235294112
      ],
      #[
        -0.48529411764705882,
        0.48529411764705882,
        0.76470588235294112,
        0,
        0,
        0.76470588235294112
      ],
      #[
        1.0441176470588236,
        -1.0441176470588236,
        0.76470588235294112,
        0,
        0,
        0.76470588235294112
      ],
      #[
        -1.0441176470588236,
        1.0592105263157894,
        0.76470588235294112,
        0,
        0,
        1.0263157894736843
      ],
      #[
        0.48529411764705882,
        -0.30921052631578949,
        0.76470588235294112,
        0,
        0,
        1.0263157894736843
      ],
      #[
        -0.48529411764705882,
        0.30921052631578949,
        0.76470588235294112,
        0,
        0,
        1.0263157894736843
      ],
      #[
        1.0441176470588236,
        -1.0592105263157894,
        0.76470588235294112,
        0,
        0,
        1.0263157894736843
      ],
      #[
        -1.0592105263157894,
        1.0441176470588236,
        1.0263157894736843,
        0,
        0,
        0.76470588235294112
      ],
      #[
        0.30921052631578949,
        -0.48529411764705882,
        1.0263157894736843,
        0,
        0,
        0.76470588235294112
      ],
      #[
        -0.30921052631578949,
        0.48529411764705882,
        1.0263157894736843,
        0,
        0,
        0.76470588235294112
      ],
      #[
        1.0592105263157894,
        -1.0441176470588236,
        1.0263157894736843,
        0,
        0,
        0.76470588235294112
      ],
      #[
        -1.0592105263157894,
        1.0592105263157894,
        1.0263157894736843,
        0,
        0,
        1.0263157894736843
      ],
      #[
        0.30921052631578949,
        -0.30921052631578949,
        1.0263157894736843,
        0,
        0,
        1.0263157894736843
      ],
      #[
        -0.30921052631578949,
        0.30921052631578949,
        1.0263157894736843,
        0,
        0,
        1.0263157894736843
      ],
      #[
        1.0592105263157894,
        -1.0592105263157894,
        1.0263157894736843,
        0,
        0,
        1.0263157894736843
      ]
    ]
  let mut index := 0
  for p0 in [15.0 / 16.0, 13.0 / 4.0] do
    for p1 in [15.0 / 16.0, 13.0 / 4.0] do
      for r0 in [1.0, 1.5] do
        for r1 in [1.0, 1.5] do
          for x in [-19.0 / 16.0, 19.0 / 16.0] do
            for z in [-1.0, 1.0] do
              let expected := references.getD index #[]
              for zero in [0.0, -0.0] do
                let input : Model :=
                  ⟨
                    2,
                    2,
                    identity 2,
                    #[1.0, zero, zero, 1.0],
                    identity 2,
                    #[r0, zero, zero, r1],
                    #[z, -z]
                  ⟩
                let prior : State := ⟨#[x, -x], #[p0, zero, zero, p1]⟩
                let output ←
                  requireOk (CovarianceFilter.update .joseph input prior)
                    "complete Joseph correction"
                check (close output.mean (expected.extract 0 2) 1.0e-14)
                  "Joseph mean exact-rational optimal-update reference"
                check (close output.covariance (expected.extract 2 6) 1.0e-14)
                  "Joseph covariance exact-rational optimal-update reference"
                check
                  (output.mean.size == 2
                    && output.covariance.size == 4
                    && output.mean.all Float.isFinite
                    && output.covariance.all Float.isFinite)
                  "Joseph correction finite storage"
                check
                  (output.covariance.getD 1 1.0 == 0.0
                    && output.covariance.getD 2 1.0 == 0.0)
                  "Joseph correction diagonal covariance"
                for i in [:2] do
                  check
                    (0.4375 ≤ output.covariance.getD (i * 2 + i) 0.0
                      && output.covariance.getD (i * 2 + i) 0.0 ≤ 1.625)
                    "Joseph corrected covariance invariant"
                  check ((output.mean.getD i 0.0).abs ≤ 1.125)
                    "Joseph corrected mean invariant"
              index := index + 1
  check (index == references.size) "Joseph correction oracle coverage"

/-- A reproducible binary64 one-step negative variance, with F=0 and Q=1 so
the full-step predicted covariance is exactly one. This is not an accumulation example. -/
def negativeVarianceChecks : IO Unit := do
  let h := Float.ofBits 0x3ffd8a8f075e6e3b
  let r := Float.ofBits 0x3c30000000000000
  let input := { scalar h r 1.0 with transition := #[0.0], measurement := #[0.0] }
  let initial : State := ⟨#[0.0], #[1.0]⟩
  for form in [CovarianceFilter.Form.compact, .subtractive] do
    let result ←
      requireOk (CovarianceFilter.step form input initial)
        "negative variance conventional"
    check (result.covariance.getD 0 0.0 == -(Float.ofBits 0x3cb0000000000000))
      "expected negative variance -2^-52"
  let stabilized ←
    requireOk (CovarianceFilter.step .joseph input initial) "negative variance Joseph"
  check (0.0 < stabilized.covariance.getD 0 0.0) "Joseph negative-variance fixture"
  let factor ←
    requireOk (SquareRootFilter.fromCovariance input initial)
      "negative fixture initialization"
  let result ←
    requireOk (SquareRootFilter.step input factor) "negative fixture square root"
  check (0.0 < result.lower.getD 0 0.0) "square-root negative-variance fixture"
  IO.println
    "Negative-variance fixture: compact/subtractive P = -2^-52; Joseph/QR positive."

/-- Native companion to the kernel-certified nine-step trace. The large
transition amplifies the covariance fed forward from preceding rounded steps. -/
def repeatedNegativeChecks : IO Unit := do
  let input : Model :=
    ⟨
      1,
      1,
      #[Float.ofBits 0x4160000000000000],
      #[Float.ofBits 0x3ffecc02dca65478],
      #[Float.ofBits 0x3d00000000000000],
      #[Float.ofBits 0x3c00000000000000],
      #[0.0]
    ⟩
  let expected : Array UInt64 :=
    #[
      0x3f80000000000000,
      0x3f10000000000000,
      0x3ea0000000000000,
      0x3e30000000000000,
      0x3dc0000000000000,
      0x3d50000000000000,
      0x3ce0000000000002,
      0x3c70000000000102,
      0xbc10000000008102
    ]
  let mut compact : State := ⟨#[0.0], #[1.0]⟩
  let mut joseph := compact
  let mut factor ←
    requireOk (SquareRootFilter.fromCovariance input compact) "trace initialization"
  for i in [:9] do
    compact ← requireOk (CovarianceFilter.step .compact input compact) "trace compact"
    joseph ← requireOk (CovarianceFilter.step .joseph input joseph) "trace Joseph"
    factor ← requireOk (SquareRootFilter.step input factor) "trace square root"
    check ((compact.covariance.getD 0 0.0).toBits == expected.getD i 0)
      "trace bit pattern"
    check
      (if i < 8 then
          0.0 < compact.covariance.getD 0 0.0
        else
          compact.covariance.getD 0 0.0 < 0.0)
      "trace delayed negativity"
    check (0.0 < joseph.covariance.getD 0 0.0) "trace Joseph positivity"
    check (factor.validate 1 matches .ok ()) "trace factor validity"
  IO.println "Nine-step fixture: first eight compact variances positive; ninth negative."

def rejectionChecks : IO Unit := do
  let base := scalar 1.0 1.0 1.0
  let state : State := ⟨#[0.0], #[1.0]⟩
  check
    (CovarianceFilter.step .compact { base with stateDimension := 0 } state
      matches .error .unsupportedDimension)
    "unsupported dimension"
  check
    (CovarianceFilter.step .compact { base with observation := #[] } state
      matches .error .invalidShape)
    "bad observation shape"
  check
    (CovarianceFilter.step .compact { base with measurement := #[Float.nan] } state
      matches .error .nonfiniteInput)
    "NaN input"
  check
    (CovarianceFilter.step .compact { base with transition := #[Float.inf] } state
      matches .error .nonfiniteInput)
    "infinite input"
  check
    (CovarianceFilter.predict { base with transition := #[1.0e308] } state
      matches .error .nonfiniteComputation)
    "prediction overflow"
  check
    (SquareRootFilter.fromCovariance base { state with covariance := #[-1.0] }
      matches .error .nonpositivePivot)
    "negative initial covariance"
  check (SquareRootFilter.step base ⟨#[0.0], #[0.0]⟩ matches .error .invalidFactor)
    "singular input factor"
  let two : Model :=
    ⟨2, 1, identity 2, #[1.0, 0.0], #[1.0, 0.25, 0.0, 1.0], #[1.0], #[0.0]⟩
  check (two.validate matches .error .nonsymmetricNoise) "asymmetric noise"

private def denseWordChecks (factor : FactorState) (output : State) : IO Unit := do
  check ((entry 2 output.covariance 0 1).toBits == (entry 2 output.covariance 1 0).toBits)
    "dense Gram exact off-diagonal word agreement"
  check (output.mean.map Float.toBits == factor.mean.map Float.toBits)
    "dense materialization preserves mean words"
  check (output.validate 2 matches .ok ()) "dense materialization finite shape"

/-- Native Sylvester regression for the simpler eighth floor. The proof uses
the exact decoded matrix and the stronger quarter-minus-2^-47 floor instead. -/
private def denseFloorChecks (output : State) : IO Unit := do
  let a := entry 2 output.covariance 0 0 - 0.125
  let b := entry 2 output.covariance 1 0
  let d := entry 2 output.covariance 1 1 - 0.125
  check (0.0 < a && 0.0 < d && 0.0 < a * d - b * b) "dense covariance eighth floor"

/-- Exercise the symmetry schedule across correlations, signed zeros, large
and tiny scales. Underflow cases intentionally have no dense-PD expectation. -/
def twoStateDenseOutputChecks : IO Unit := do
  for lower
      in #[
        #[1.0, 0.0, 0.25, 1.25],
        #[1.0, -0.0, -0.25, 1.25],
        #[1.0, -0.0, -0.0, 1.0],
        #[1.0e120, 0.0, -1.0e-120, 1.0],
        #[1.0e-160, -0.0, -0.5e-160, 2.0e-160],
        #[1.0e-180, 0.0, -0.5e-180, 2.0e-180]
      ] do
    let factor : FactorState := ⟨#[-0.0, 0.5], lower⟩
    let output ←
      requireOk (SquareRootFilter.materialize 2 factor) "dense symmetry schedule"
    denseWordChecks factor output
  check
    (SquareRootFilter.materialize 2 ⟨#[0.0, 0.0], #[1.0e200, 0.0, 0.0, 1.0]⟩
      matches .error .nonfiniteComputation)
    "dense Gram overflow rejection"

/-- Long original-input trajectory against a separately generated 120-digit
Decimal ideal recursion. The manual generator is Tests/HorizonReference.py;
it also checks the exact Joseph/subtractive identity to 110 decimal places.
The 1e-12 tolerance is a regression criterion, not the formal error allowance. -/
def originalInputHorizonChecks : IO Unit := do
  let q0 := #[1.0, 0.25, 0.25, 1.5]
  let q1 := #[1.5, -0.25, -0.25, 1.0]
  let inputs :=
    fun t =>
      {
        stateDimension := 2,
        measurementDimension := 2,
        transition := #[0.125, 0.0625, -0.03125, 0.125],
        observation := #[0.015625, -0.0078125, 0.00390625, 0.015625],
        processNoise := if t % 2 == 0 then q0 else q1,
        measurementNoise := if t % 3 == 0 then q1 else q0,
        measurement := if t % 2 == 0 then #[1.0, -1.0] else #[-1.0, 1.0] : Model
      }
  let initial : State := ⟨#[0.25, -0.75], q0⟩
  let checkpoints : Array (Nat × Array Float × Array Float) :=
    #[
      (
        1,
        #[
          1.0251471446321754,
          0.26104785211939946,
          0.26104785211939946,
          1.5218439091513039
        ],
        #[-0.015349086684803262, -0.12716047848703865]
      ),
      (
        2,
        #[
          1.525368724095544,
          -0.23819262116827106,
          -0.23819262116827106,
          1.0223785367664906
        ],
        #[-0.039201706472264716, 0.011924073280958864]
      ),
      (
        3,
        #[
          1.0238949073689287,
          0.24880326008775874,
          0.24880326008775874,
          1.5187654816904639
        ],
        #[0.0060976501517847346, -0.028478641235769469]
      ),
      (
        8,
        #[
          1.5251418986977063,
          -0.23838216729420958,
          -0.23838216729420958,
          1.0224255599097321
        ],
        #[-0.030922649039569646, 0.024674799931365437]
      ),
      (
        32,
        #[
          1.5251418986977137,
          -0.23838216729420897,
          -0.23838216729420897,
          1.0224255599097265
        ],
        #[-0.030922582033654961, 0.024674740435118792]
      ),
      (
        128,
        #[
          1.5251418986977137,
          -0.23838216729420897,
          -0.23838216729420897,
          1.0224255599097265
        ],
        #[-0.030922582033654961, 0.024674740435118792]
      ),
      (
        256,
        #[
          1.5253338152064471,
          -0.23862080278250089,
          -0.23862080278250089,
          1.022516421804484
        ],
        #[-0.012173668170726765, 0.015555639663472939]
      ),
    ]
  let retained ←
    requireOk (SquareRootFilter.fromCovariance (inputs 0) initial)
      "high-precision horizon initialization"
  let initialDense ←
    requireOk (SquareRootFilter.materialize 2 retained) "initial dense conversion"
  denseWordChecks retained initialDense
  denseFloorChecks initialDense
  let mut current := retained
  for t in [:256] do
    current ←
      requireOk (SquareRootFilter.step (inputs t) current) "high-precision horizon step"
    check (current.validate 2 matches .ok ()) "high-precision horizon factor validation"
    check
      (current.mean.all (fun v => v.abs ≤ 1.0)
        && current.lower.all (fun v => v.abs ≤ 2.0))
      "high-precision horizon stored invariant"
    let represented ←
      requireOk (SquareRootFilter.materialize 2 current)
        "high-precision horizon Gram regression"
    denseWordChecks current represented
    denseFloorChecks represented
    check (represented.covariance.all (fun v => v.abs ≤ 2.0))
      "high-precision horizon covariance cap"
    for (count, covariance, mean) in checkpoints do
      if count == t + 1 then
        check
          (close represented.covariance covariance 1.0e-12
            && close represented.mean mean 1.0e-12)
          "independent 120-digit ideal horizon reference"
  let driven ←
    requireOk (SquareRootFilter.run inputs retained 256) "high-precision horizon driver"
  check
    (driven.lower.map Float.toBits == current.lower.map Float.toBits
      && driven.mean.map Float.toBits == current.mean.map Float.toBits)
    "high-precision horizon driver bit agreement"

/-- A nontrivial small-gain companion to the conditional two-state budget.
Agreement with a separately evaluated native Joseph recursion supplements the
proof; it does not discharge the Real reached-prefix domain by itself. -/
def filterHorizonChecks : IO Unit := do
  let base : Model :=
    ⟨
      2,
      2,
      #[1.0 / 64.0, 1.0 / 128.0, -1.0 / 128.0, 1.0 / 64.0],
      #[1.0 / 32.0, -1.0 / 64.0, 1.0 / 64.0, 1.0 / 32.0],
      identity 2,
      identity 2,
      #[0.5, -0.5]
    ⟩
  let mut dense : State := ⟨#[1.0, -1.0], #[1.0, 0.125, 0.125, 1.0]⟩
  let mut factor ←
    requireOk (SquareRootFilter.fromCovariance base dense) "horizon initialization"
  for t in [:400] do
    let input :=
      { base with measurement := if t % 2 == 0 then #[0.5, -0.5] else #[-0.5, 0.5] }
    dense ← requireOk (CovarianceFilter.step .joseph input dense) "horizon Joseph"
    factor ← requireOk (SquareRootFilter.step input factor) "horizon square root"
    let materialized ←
      requireOk (SquareRootFilter.materialize 2 factor) "horizon materialization"
    check
      (close materialized.covariance dense.covariance
        && close materialized.mean dense.mean)
      "400-step covariance and mean agreement"
    check (factor.validate 2 matches .ok ()) "400-step factor validity"
    check (materialized.mean.all (fun x => x.abs ≤ 1.0)) "400-step mean magnitude"
  let reset : Model :=
    ⟨
      2,
      2,
      #[0.0, 0.0, 0.0, 0.0],
      #[0.0, 0.0, 0.0, 0.0],
      identity 2,
      identity 2,
      #[1.0, 0.0]
    ⟩
  let retained : FactorState := ⟨#[0.0, 0.0], #[1.0, 0.0, -0.0, 1.0]⟩
  let result ← requireOk (SquareRootFilter.step reset retained) "reset domain witness"
  check (result.lower.map Float.toBits == retained.lower.map Float.toBits)
    "reset retained signed-zero certificate"
  check (result.mean.map Float.toBits == retained.mean.map Float.toBits)
    "reset mean certificate"
  let traceResult ←
    requireOk (SquareRootFilter.run (fun _ => reset) retained 32) "checked trace driver"
  check (traceResult.lower.map Float.toBits == retained.lower.map Float.toBits)
    "trace driver signed-zero certificate"
  let invalid := { reset with measurement := #[Float.nan, 0.0] }
  check
    (SquareRootFilter.run (fun t => if t == 1 then invalid else reset) retained 3
      matches .error .nonfiniteInput)
    "trace driver prefix error propagation"

/-- Disjoint-support QR, including subnormal and large finite operands. -/
private def diagonalQRScaleChecks : IO Unit := do
  let scales : Array Float := #[Float.ofBits 1, 1.0e-300, 1.0, 1.0e300]
  let mut cases := 0
  for scale in scales do
    let blocks : Array (Array Float × Array Float) :=
      #[
        (#[3.0 * scale, -0.0, 0.0, -2.0 * scale], #[4.0 * scale, 0.0, -0.0, 0.0]),
        (#[0.0, -0.0, 0.0, 0.0], #[-5.0 * scale, 0.0, -0.0, 2.0 * scale]),
        (#[-3.0 * scale, 0.0, -0.0, 0.0], #[-4.0 * scale, -0.0, 0.0, -2.0 * scale])
      ]
    for (a, b) in blocks do
      let l ←
        requireOk (OrthogonalFactorization.gramFactor 2 4 (fromCols 2 2 2 a b))
          "disjoint-support QR across binary64 scales"
      check (l.size == 4 && l.all Float.isFinite) "diagonal QR finite storage"
      check (entry 2 l 0 1 == 0.0 && entry 2 l 1 0 == 0.0) "diagonal QR decoded zeros"
      check (0.0 < entry 2 l 0 0 && 0.0 < entry 2 l 1 1) "diagonal QR retained signs"
      check (close #[entry 2 l 0 0 / scale, entry 2 l 1 1 / scale] #[5.0, 2.0] 1.0e-12)
        "diagonal QR independently known scaled 3-4-5 norm"
      cases := cases + 1
  check (cases == 12) "diagonal QR scale grid size"
  check
    (OrthogonalFactorization.gramFactor 2 4
        (fromCols 2 2 2 #[1.0, -0.0, 0.0, 0.0] #[2.0, 0.0, -0.0, -0.0])
      matches .error .nonpositivePivot)
    "diagonal QR rank rejection"

/-- Larger diagonal solve domain, including correlated RHSs at the cap and
signed-zero/subnormal RHS entries. The reference divides directly by d²,
independently of the native forward/backward substitution schedule. -/
private def diagonalSolveChecks : IO Unit := do
  let diagonals : Array Float := #[1.0, 1.25, 2.25]
  let tiny := Float.ofBits 1
  let rightHandSides : Array (Array Float) :=
    #[
      #[4.0, 4.0, -4.0, -4.0],
      #[-4.0, 4.0, 4.0, -4.0],
      #[4.0, -0.0, 0.0, -4.0],
      #[tiny, -tiny, tiny, -tiny],
      #[tiny, -0.0, 0.0, -tiny],
      #[0.0, -0.0, -0.0, 0.0]
    ]
  let mut cases := 0
  for d0 in diagonals do
    for d1 in diagonals do
      let l := #[d0, -0.0, 0.0, d1]
      for b in rightHandSides do
        let y ← requireOk (forwardCholesky 2 2 l b) "larger diagonal forward solve"
        let x ← requireOk (backwardCholesky 2 2 l y) "larger diagonal backward solve"
        let result ← requireOk (solveCholesky 2 2 l b) "larger diagonal composed solve"
        check (result.map Float.toBits == x.map Float.toBits)
          "composed substitution word agreement"
        check (y.size == 4 && y.all Float.isFinite && y.all (fun v => v.abs ≤ 5.0))
          "larger diagonal forward storage/cap"
        check (x.size == 4 && x.all Float.isFinite && x.all (fun v => v.abs ≤ 6.0))
          "larger diagonal backward storage/cap"
        let expected :=
          #[
            entry 2 b 0 0 / (d0 * d0),
            entry 2 b 0 1 / (d0 * d0),
            entry 2 b 1 0 / (d1 * d1),
            entry 2 b 1 1 / (d1 * d1)
          ]
        check (close result expected 1.0e-12)
          "larger diagonal independent solve reference"
        if entry 2 b 0 1 == 0.0 && entry 2 b 1 0 == 0.0 then
          check (entry 2 result 0 1 == 0.0 && entry 2 result 1 0 == 0.0)
            "larger diagonal solve decoded zeros"
        cases := cases + 1
  check (cases == 54) "larger diagonal solve grid size"

/-- Stored diagonal gains at both proved endpoints, with slack mean endpoints,
same/opposite-sign measurements, signed zeros and subnormal means. The reference
uses the weighted scalar formula rather than residual/increment evaluation. -/
private def observableMeanChecks : IO Unit := do
  let gains : Array Float := #[0.375, 0.5, 0.8125]
  let tiny := Float.ofBits 1
  let means : Array (Array Float) :=
    #[
      #[1.1875, -1.1875],
      #[-1.1875, 1.1875],
      #[1.1875, 1.1875],
      #[-1.1875, -1.1875],
      #[0.0, -0.0],
      #[tiny, -tiny]
    ]
  let measurements : Array (Array Float) :=
    #[#[1.0, -1.0], #[-1.0, 1.0], #[1.0, 1.0], #[-1.0, -1.0], #[-0.0, 0.0]]
  let mut cases := 0
  for k0 in gains do
    for k1 in gains do
      let k := #[k0, -0.0, 0.0, k1]
      for mean in means do
        for measurement in measurements do
          let projected ←
            requireOk (multiply 2 2 1 (identity 2) mean) "observable mean projection"
          let residual ← requireOk (sub measurement projected) "observable mean residual"
          let increment ←
            requireOk (multiply 2 2 1 k residual) "observable mean increment"
          let output ← requireOk (add mean increment) "observable mean addition"
          check (projected.all (fun x => x.abs ≤ 1.25)) "observable projected mean cap"
          check (residual.all (fun x => x.abs ≤ 2.375)) "observable residual cap"
          check (increment.all (fun x => x.abs ≤ 2.0)) "observable increment cap"
          check
            (output.size == 2
              && output.all Float.isFinite
              && output.all (fun x => x.abs ≤ 1.125))
            "observable returned mean storage/cap"
          check
            (close output
              #[
                (1.0 - k0) * mean.getD 0 0.0 + k0 * measurement.getD 0 0.0,
                (1.0 - k1) * mean.getD 1 0.0 + k1 * measurement.getD 1 0.0
              ] 1.0e-12)
            "observable independent weighted mean"
          cases := cases + 1
  check (cases == 270) "observable stored-gain mean grid size"

/-- Local covariance/mean boundary cases complement the reached prediction grid. -/
private def observablePosteriorChecks : IO Unit := do
  let diagonals : Array Float := #[0.96875, 1.25, 1.8]
  let noises : Array Float := #[1.0, 1.5]
  let means : Array (Array Float) :=
    #[#[1.1875, -1.1875], #[-1.1875, 1.1875], #[Float.ofBits 1, -0.0]]
  let measurements : Array (Array Float) := #[#[1.0, -1.0], #[-1.0, 1.0]]
  let mut cases := 0
  for l0 in diagonals do
    for l1 in diagonals do
      for r0 in noises do
        for r1 in noises do
          for mean in means do
            for z in measurements do
              let input : Model :=
                ⟨2, 2, identity 2, identity 2, identity 2, #[r0, -0.0, 0.0, r1], z⟩
              let prior : FactorState := ⟨mean, #[l0, -0.0, 0.0, l1]⟩
              let result ←
                requireOk (SquareRootFilter.update input prior)
                  "observable local correction"
              check (result.validate 2 matches .ok ())
                "observable local factor validation"
              check
                (result.mean.all (fun x => x.abs ≤ 1.125)
                  && result.lower.all (fun x => x.abs ≤ 1.125))
                "observable local returned caps"
              check (entry 2 result.lower 0 1 == 0.0 && entry 2 result.lower 1 0 == 0.0)
                "observable local returned diagonal support"
              let dense ←
                requireOk (SquareRootFilter.materialize 2 result)
                  "observable local covariance"
              let p0 := l0 * l0
              let p1 := l1 * l1
              let k0 := p0 / (p0 + r0)
              let k1 := p1 / (p1 + r1)
              check
                (close dense.covariance
                  #[p0 * r0 / (p0 + r0), 0.0, 0.0, p1 * r1 / (p1 + r1)] 1.0e-12)
                "observable local scalar posterior reference"
              check
                (close result.mean
                  #[
                    (1.0 - k0) * mean.getD 0 0.0 + k0 * z.getD 0 0.0,
                    (1.0 - k1) * mean.getD 1 0.0 + k1 * z.getD 1 0.0
                  ] 1.0e-12)
                "observable local scalar mean reference"
              check
                (0.4375 ≤ dense.covariance.getD 0 0.0
                  && dense.covariance.getD 0 0.0 ≤ 1.0625
                  && 0.4375 ≤ dense.covariance.getD 3 0.0
                  && dense.covariance.getD 3 0.0 ≤ 1.0625)
                "observable local covariance margins"
              cases := cases + 1
  check (cases == 216) "observable local correction grid size"

/-- Larger diagonal dynamics, including identity, sign reversal and reset.
The diagonal subset checks gain, mean and posterior covariance correction
against scalar formulas. These regressions supplement the local proofs. -/
private def observablePredictionInnovationChecks : IO Unit := do
  let transitions : Array Float := #[-1.0, -0.875, 0.0, 0.875, 1.0]
  let noises : Array Float := #[1.0, 1.5]
  let factors : Array (Array Float) :=
    #[
      #[1.0, 0.0, 0.0, 1.0],
      #[1.25, 0.0, 0.25, 1.25],
      #[1.25, -0.0, -0.25, 1.25],
      #[0.75, -0.0, 0.0, 0.75]
    ]
  let means : Array (Array Float) := #[#[1.125, -1.125], #[-1.0, 1.0], #[-0.0, 0.0]]
  let mut cases := 0
  let mut gainCases := 0
  for f0 in transitions do
    for f1 in transitions do
      for q0 in noises do
        for q1 in noises do
          let input : Model :=
            ⟨
              2,
              2,
              #[f0, -0.0, 0.0, f1],
              identity 2,
              #[q0, -0.0, 0.0, q1],
              #[q1, 0.0, -0.0, q0],
              #[1.0, -1.0]
            ⟩
          for lower in factors do
            let l0 := lower.getD 0 0.0
            let c := lower.getD 2 0.0
            let l1 := lower.getD 3 0.0
            for mean in means do
              let initial : FactorState := ⟨mean, lower⟩
              let fl ← requireOk (multiply 2 2 2 input.transition lower) "observable FL"
              let tq ←
                requireOk (cholesky 2 input.processNoise) "diagonal process Cholesky"
              check (entry 2 tq 0 1 == 0.0 && entry 2 tq 1 0 == 0.0)
                "Cholesky decoded zeros"
              if c == 0.0 then
                check (entry 2 fl 0 1 == 0.0 && entry 2 fl 1 0 == 0.0) "FL decoded zeros"
              let predicted ←
                requireOk (SquareRootFilter.predict input initial) "observable prediction"
              check (predicted.validate 2 matches .ok ())
                "observable prediction output validation"
              check (predicted.mean.all (fun x => x.abs ≤ 1.1875))
                "observable prediction mean cap"
              check (predicted.lower.all (fun x => x.abs ≤ 2.0))
                "observable prediction factor cap"
              if c == 0.0 then
                check
                  (entry 2 predicted.lower 0 1 == 0.0
                    && entry 2 predicted.lower 1 0 == 0.0)
                  "observable prediction QR decoded zeros"
              let dense ←
                requireOk (SquareRootFilter.materialize 2 predicted)
                  "observable prior Gram"
              let off := f0 * f1 * l0 * c
              let expected :=
                #[
                  f0 * f0 * l0 * l0 + q0,
                  off,
                  off,
                  f1 * f1 * (c * c + l1 * l1) + q1
                ]
              check (close dense.covariance expected 1.0e-12)
                "observable analytic prediction"
              check
                (close predicted.mean #[f0 * mean.getD 0 0.0, f1 * mean.getD 1 0.0]
                  1.0e-12)
                "observable analytic mean"
              check
                (dense.covariance.getD 0 0.0 ≤ 3.25 && dense.covariance.getD 3 0.0 ≤ 3.25)
                "observable prior diagonal cap"
              let tr ←
                requireOk (cholesky 2 input.measurementNoise)
                  "diagonal measurement Cholesky"
              let hl ←
                requireOk (multiply 2 2 2 input.observation predicted.lower)
                  "observable HL"
              let s ←
                requireOk (OrthogonalFactorization.gramFactor 2 4 (fromCols 2 2 2 tr hl))
                  "observable innovation QR"
              check (s.size == 4 && s.all Float.isFinite && s.all (fun x => x.abs ≤ 2.25))
                "observable innovation factor bounds"
              let innovation ←
                requireOk (SquareRootFilter.materialize 2 ⟨predicted.mean, s⟩)
                  "observable innovation Gram"
              check
                (close innovation.covariance
                  #[expected.getD 0 0.0 + q1, off, off, expected.getD 3 0.0 + q0] 1.0e-12)
                "observable analytic innovation"
              let a := innovation.covariance.getD 0 0.0 - 1.8125
              let b := innovation.covariance.getD 1 0.0
              let d := innovation.covariance.getD 3 0.0 - 1.8125
              check (0.0 < a && 0.0 < d && 0.0 < a * d - b * b)
                "observable innovation covariance floor"
              if c == 0.0 then
                let pht ←
                  requireOk (multiply 2 2 2 predicted.lower (transpose 2 2 hl))
                    "observable PHT"
                check (pht.all (fun x => x.abs ≤ 3.5)) "observable formed RHS cap"
                let solution ←
                  requireOk (solveCholesky 2 2 s (transpose 2 2 pht))
                    "observable gain solve"
                let gain := transpose 2 2 solution
                check (gain.size == 4 && gain.all Float.isFinite)
                  "observable gain storage"
                check (entry 2 gain 0 1 == 0.0 && entry 2 gain 1 0 == 0.0)
                  "observable gain decoded zeros"
                check
                  (close gain
                    #[
                      expected.getD 0 0.0 / (expected.getD 0 0.0 + q1),
                      0.0,
                      0.0,
                      expected.getD 3 0.0 / (expected.getD 3 0.0 + q0)
                    ] 1.0e-12)
                  "observable independent scalar gain"
                check
                  (0.375 ≤ entry 2 gain 0 0
                    && entry 2 gain 0 0 ≤ 0.8125
                    && 0.375 ≤ entry 2 gain 1 1
                    && entry 2 gain 1 1 ≤ 0.8125)
                  "observable gain diagonal range"
                let projected ←
                  requireOk (multiply 2 2 1 input.observation predicted.mean)
                    "observable reached projection"
                let residual ←
                  requireOk (sub input.measurement projected)
                    "observable reached residual"
                let increment ←
                  requireOk (multiply 2 2 1 gain residual) "observable reached increment"
                let output ←
                  requireOk (add predicted.mean increment) "observable reached mean"
                check
                  (output.size == 2
                    && output.all Float.isFinite
                    && output.all (fun x => x.abs ≤ 1.125))
                  "observable reached returned mean invariant"
                let k0 := expected.getD 0 0.0 / (expected.getD 0 0.0 + q1)
                let k1 := expected.getD 3 0.0 / (expected.getD 3 0.0 + q0)
                check
                  (close output
                    #[
                      (1.0 - k0) * (f0 * mean.getD 0 0.0)
                      + k0 * input.measurement.getD 0 0.0,
                      (1.0 - k1) * (f1 * mean.getD 1 0.0)
                      + k1 * input.measurement.getD 1 0.0
                    ] 1.0e-12)
                  "observable independent ideal mean correction"
                let kh ←
                  requireOk (multiply 2 2 2 gain input.observation)
                    "observable posterior KH"
                let w ← requireOk (sub (identity 2) kh) "observable posterior complement"
                let wl ←
                  requireOk (multiply 2 2 2 w predicted.lower) "observable posterior WL"
                let ktr ← requireOk (multiply 2 2 2 gain tr) "observable posterior KTR"
                check (entry 2 w 0 1 == 0.0 && entry 2 w 1 0 == 0.0)
                  "observable complement decoded zeros"
                let postLower ←
                  requireOk
                    (OrthogonalFactorization.gramFactor 2 4 (fromCols 2 2 2 wl ktr))
                    "observable posterior QR"
                check (entry 2 postLower 0 1 == 0.0 && entry 2 postLower 1 0 == 0.0)
                  "observable posterior QR decoded zeros"
                check
                  (postLower.all Float.isFinite && postLower.all (fun x => x.abs ≤ 1.125))
                  "observable posterior factor cap"
                let corrected ←
                  requireOk (SquareRootFilter.update input predicted)
                    "observable correction"
                check (corrected.mean == output && corrected.lower == postLower)
                  "observable complete correction operation order"
                check (corrected.validate 2 matches .ok ())
                  "observable correction output validation"
                let postDense ←
                  requireOk (SquareRootFilter.materialize 2 corrected)
                    "observable posterior Gram"
                let v0 := expected.getD 0 0.0 * q1 / (expected.getD 0 0.0 + q1)
                let v1 := expected.getD 3 0.0 * q0 / (expected.getD 3 0.0 + q0)
                check (close postDense.covariance #[v0, 0.0, 0.0, v1] 1.0e-12)
                  "observable independent ideal posterior covariance"
                check
                  (0.4375 ≤ postDense.covariance.getD 0 0.0
                    && postDense.covariance.getD 0 0.0 ≤ 1.0625
                    && 0.4375 ≤ postDense.covariance.getD 3 0.0
                    && postDense.covariance.getD 3 0.0 ≤ 1.0625)
                  "observable posterior covariance margins"
                let full ←
                  requireOk (SquareRootFilter.step input initial)
                    "observable full checked step"
                check (full.mean == corrected.mean && full.lower == corrected.lower)
                  "observable full-step prediction/correction composition"
                gainCases := gainCases + 1
              cases := cases + 1
  check (cases == 1200) "observable regression grid size"
  check (gainCases == 600) "observable gain regression grid size"
  check
    (multiply 2 2 2 #[1.0e308, -0.0, 0.0, 1.0] #[2.0, 0.0, -0.0, 1.0]
      matches .error .nonfiniteComputation)
    "diagonal overflow rejection"

/-- Dense original words exercise initialization and the first complete step. -/
private def observableInitializationChecks : IO Unit := do
  let input : Model :=
    ⟨2, 2, identity 2, identity 2, identity 2, identity 2, #[1.0, -1.0]⟩
  let mut cases := 0
  for p0 in #[1.0, 1.25, 1.5] do
    for p1 in #[1.0, 1.25, 1.5] do
      for x0 in #[-1.0, 0.0, 1.0] do
        for x1 in #[-1.0, 0.0, 1.0] do
          for signed in #[false, true] do
            let covariance :=
              if signed then #[p0, -0.0, 0.0, p1] else #[p0, 0.0, -0.0, p1]
            let initial : State := ⟨#[x0, x1], covariance⟩
            let factor ←
              requireOk (SquareRootFilter.fromCovariance input initial)
                "observable original dense initialization"
            check (factor.validate 2 matches .ok ()) "observable initialized validation"
            check (factor.mean.map Float.toBits == initial.mean.map Float.toBits)
              "observable initialized exact mean words"
            check (entry 2 factor.lower 0 1 == 0.0 && entry 2 factor.lower 1 0 == 0.0)
              "observable initialized diagonal factor"
            let dense ←
              requireOk (SquareRootFilter.materialize 2 factor)
                "observable initialized dense materialization"
            check (close dense.covariance covariance 1.0e-14)
              "observable initialized original covariance reference"
            check
              (dense.covariance.all (fun x => x.abs ≤ 1.625)
                && 0.4375 ≤ entry 2 dense.covariance 0 0
                && 0.4375 ≤ entry 2 dense.covariance 1 1)
              "observable initialized covariance invariant"
            let output ←
              requireOk (SquareRootFilter.step input factor)
                "observable first step from dense initialization"
            check (output.validate 2 matches .ok ()) "observable first-step validation"
            cases := cases + 1
  check (cases == 162) "observable initialization grid size"

/-- Materialization covers the larger mean cap and both signed-zero positions. -/
private def observableDenseOutputChecks : IO Unit := do
  let mut cases := 0
  for l0 in #[0.75, 1.0, 1.25] do
    for l1 in #[0.75, 1.0, 1.25] do
      for x in #[-1.125, -0.0, 1.125] do
        for z0 in #[0.0, -0.0] do
          for z1 in #[0.0, -0.0] do
            let factor : FactorState := ⟨#[x, -x], #[l0, z0, z1, l1]⟩
            let output ←
              requireOk (SquareRootFilter.materialize 2 factor)
                "observable larger-invariant dense output"
            denseWordChecks factor output
            check (close output.covariance #[l0 * l0, 0.0, 0.0, l1 * l1] 1.0e-14)
              "observable dense diagonal polynomial reference"
            let a := entry 2 output.covariance 0 0 - 0.375
            let b := entry 2 output.covariance 1 0
            let c := entry 2 output.covariance 1 1 - 0.375
            check (0.0 < a && 0.0 < c && 0.0 < a * c - b * b)
              "observable dense three-eighths floor"
            cases := cases + 1
  check (cases == 108) "observable dense output grid size"

/-- A separate 120/160-digit ideal diagonal oracle supplements the completed
native execution invariant. Accumulated ideal-trajectory error is still separate. -/
private def observableHorizonChecks : IO Unit := do
  let inputs (t : Nat) : Model :=
    let f0 : Float := if t % 3 == 0 then 1.0 else 0.9990234375
    let f1 : Float :=
      match t % 4 with
      | 0 => 1.0
      | 1 => -1.0
      | 2 => 0.99609375
      | _ => -0.9990234375
    let q := if t % 2 == 0 then #[1.0, -0.0, 0.0, 1.5] else #[1.5, 0.0, -0.0, 1.0]
    let r := if t % 3 == 0 then #[1.5, -0.0, 0.0, 1.0] else #[1.0, 0.0, -0.0, 1.5]
    let z := if t % 2 == 0 then #[1.0, -1.0] else #[-1.0, 1.0]
    ⟨2, 2, #[f0, -0.0, 0.0, f1], identity 2, q, r, z⟩
  let denseInitial : State := ⟨#[1.0, -1.0], #[1.25, -0.0, 0.0, 1.5]⟩
  let initial ←
    requireOk (SquareRootFilter.fromCovariance (inputs 0) denseInitial)
      "observable horizon original dense initialization"
  let checkpoints : Array (Nat × Array Float × Array Float) :=
    #[
      (1, #[0.90000000000000002, 0, 0, 0.75], #[1, -1]),
      (2, #[0.70573028870495103, 0, 0, 0.80769230769230771], #[-0.41174795017483856, 1]),
      (
        3,
        #[0.63022573071444954, 0, 0, 0.90811194977933052],
        #[0.4781206186577544, -0.21235730816989029]
      ),
      (
        8,
        #[0.69618704312857449, 0, 0, 0.79648302818317451],
        #[-0.609905447402314, 0.76264892160205833]
      ),
      (
        32,
        #[0.69618698782963684, 0, 0, 0.79648289970878128],
        #[-0.61039433630328377, 0.76344383132899962]
      ),
      (
        128,
        #[0.69618698782963684, 0, 0, 0.79648289970878128],
        #[-0.61039433630330031, 0.76344383132911364]
      ),
      (
        256,
        #[0.87998061414245898, 0, 0, 0.65572690379403598],
        #[-0.42022643641488344, 0.76000558552228081]
      ),
    ]
  let checkInvariant (current : FactorState) : IO Unit := do
    check (current.validate 2 matches .ok ()) "observable horizon factor validation"
    check
      (current.mean.all (fun x => x.abs ≤ 1.125)
        && current.lower.all (fun x => x.abs ≤ 2.0))
      "observable horizon storage caps"
    check (entry 2 current.lower 0 1 == 0.0 && entry 2 current.lower 1 0 == 0.0)
      "observable horizon decoded diagonal support"
    let dense ←
      requireOk (SquareRootFilter.materialize 2 current)
        "observable horizon materialization"
    denseWordChecks current dense
    let a := entry 2 dense.covariance 0 0 - 0.375
    let b := entry 2 dense.covariance 1 0
    let c := entry 2 dense.covariance 1 1 - 0.375
    check (0.0 < a && 0.0 < c && 0.0 < a * c - b * b)
      "observable horizon dense three-eighths floor"
    check
      (0.4375 ≤ entry 2 dense.covariance 0 0
        && entry 2 dense.covariance 0 0 ≤ 1.625
        && 0.4375 ≤ entry 2 dense.covariance 1 1
        && entry 2 dense.covariance 1 1 ≤ 1.625)
      "observable horizon covariance invariant"
  let mut current := initial
  checkInvariant current
  for t in [:256] do
    current ←
      requireOk (SquareRootFilter.step (inputs t) current)
        "observable checked horizon step"
    checkInvariant current
    for (count, covariance, mean) in checkpoints do
      if count == t + 1 then
        let dense ←
          requireOk (SquareRootFilter.materialize 2 current)
            "observable reference covariance"
        check
          (close dense.covariance covariance 1.0e-12 && close current.mean mean 1.0e-12)
          "observable independent 120/160-digit ideal reference"
  let driven ←
    requireOk (SquareRootFilter.run inputs initial 256) "observable horizon trace driver"
  check
    (driven.mean.map Float.toBits == current.mean.map Float.toBits
      && driven.lower.map Float.toBits == current.lower.map Float.toBits)
    "observable horizon driver exact retained words"

def run : IO Unit := do
  scalarChecks
  correlatedChecks
  mixedObservationChecks
  rectangularChecks
  qrChecks
  choleskySolveChecks
  choleskyInputDomainChecks
  choleskySolveDomainChecks
  qrNormChecks
  qrReflectorChecks
  qrApplicationChecks
  qrFinishChecks
  qrIterationChecks
  qrRetentionChecks
  qrTriangularChecks
  qrGramChecks
  qrCompositionChecks
  qrSourceTailChecks
  qrInitialDomainChecks
  qrFactorSolveDomainChecks
  gainInputDomainChecks
  innovationInputDomainChecks
  meanInputDomainChecks
  predictionInputDomainChecks
  posteriorInputDomainChecks
  cancellationChecks
  josephStoredInputChecks
  josephDiagonalSolveChecks
  josephDiagonalPositiveChecks
  josephComputedGainChecks
  josephCompleteUpdateChecks
  negativeVarianceChecks
  repeatedNegativeChecks
  filterHorizonChecks
  originalInputHorizonChecks
  twoStateDenseOutputChecks
  diagonalQRScaleChecks
  diagonalSolveChecks
  observableMeanChecks
  observablePosteriorChecks
  observablePredictionInnovationChecks
  observableInitializationChecks
  observableDenseOutputChecks
  observableHorizonChecks
  rejectionChecks
  IO.println
    "All Kalman native regression groups passed (including 100 rectangular and 400 covariance/mean steps)."

end Kalman.Tests.FloatImplementations

def main : IO Unit := Kalman.Tests.FloatImplementations.run
