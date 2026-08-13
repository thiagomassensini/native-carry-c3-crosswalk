import NativeCarryC3Crosswalk.C3BoundaryJetCore
import NativeCarryC3Crosswalk.FinitePackaging

/-!
# Explicit C3 fifth-order oriented boundary jet

This module materializes the boundary correction used by the certified C3
residual ledgers.  It does not choose a corrected stationary center and does
not assert convergence of the resulting core error.
-/

namespace NativeCarryC3Crosswalk

open FiniteNativeCarryOperator
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-- Forget the complex packaging and recover its two real coordinates. -/
def unpackComplex : ℂ →+ Operator.RealPlane where
  toFun z := (z.re, z.im)
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem package_unpackComplex (z : ℂ) :
    CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
        (unpackComplex z) = z := by
  rfl

@[simp] theorem unpackComplex_package (u : Operator.RealPlane) :
    unpackComplex
        (CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging u) = u := by
  rfl

/-- Finite C3 resultant corrected by the explicit oriented boundary jet. -/
def c3CorrectedRealResidual (cutoff : ℕ) (time : ℝ) :
    Operator.RealPlane :=
  Operator.finiteNativeOperator 3 cutoff time +
    unpackComplex (c3OrientedBoundaryJet cutoff (nativeLine time))

/-- Complex presentation of the same corrected finite residual. -/
def c3CorrectedCharacteristic (cutoff : ℕ) (time : ℝ) : ℂ :=
  finiteBracketCharacteristic 3 cutoff (nativeLine time) +
    c3OrientedBoundaryJet cutoff (nativeLine time)

/-- The corrected real residual packages exactly to the corrected chart. -/
theorem package_c3CorrectedRealResidual
    (cutoff : ℕ) (time : ℝ) :
    CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
        (c3CorrectedRealResidual cutoff time) =
      c3CorrectedCharacteristic cutoff time := by
  simp [c3CorrectedRealResidual, c3CorrectedCharacteristic,
    packaged_finiteNativeOperator_eq_finiteBracketCharacteristic]

/-- The scalar core error used as `Q_M` once a center has been selected. -/
def c3CorrectedCoreError (cutoff : ℕ) (time : ℝ) : ℝ :=
  ‖c3CorrectedCharacteristic cutoff time‖

theorem c3CorrectedCoreError_nonneg (cutoff : ℕ) (time : ℝ) :
    0 ≤ c3CorrectedCoreError cutoff time :=
  norm_nonneg _

/-- The corrected complex norm square is the real quadratic energy exactly. -/
theorem normSq_c3CorrectedCharacteristic_eq_realEnergy
    (cutoff : ℕ) (time : ℝ) :
    Complex.normSq (c3CorrectedCharacteristic cutoff time) =
      CPFormal.Analytic.Cp.nativeCarryRealPlaneEnergy
        (c3CorrectedRealResidual cutoff time) := by
  rw [← package_c3CorrectedRealResidual]
  exact CPFormal.Analytic.Cp.normSq_nativeCarryRealPlaneComplexPackaging _

end

end NativeCarryC3Crosswalk
