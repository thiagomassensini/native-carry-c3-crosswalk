import NativeCarryC3Crosswalk.C3BoundaryJet
import NativeCarryC3Crosswalk.C3BoundaryJetDerivativeCore
import NativeCarrySpectralWeyl.Camera.DerivativeTail
import FiniteNativeCarryOperator.Operator.Score

/-!
# Corrected C3 velocity and stationary equation

This module materializes the first corrected time derivative from the C3
stationary-localization ledger.  It proves that the real velocity is the
derivative of the corrected resultant and that the stationary numerator is
one half of the derivative of its quadratic energy.

No stationary center is selected here.
-/

namespace NativeCarryC3Crosswalk

open FiniteNativeCarryOperator
open NativeCarrySpectralWeyl.Camera

noncomputable section

/--
Real derivative into the canonical normed real presentation of `ℂ` selected
by the imported analytic stack.  This abbreviation is the ordinary
`HasDerivAt` predicate with its bundled instances made explicit.
-/
abbrev RealComplexHasDerivAt (f : ℝ → ℂ) (f' : ℂ) (x : ℝ) : Prop :=
  @HasDerivAt ℝ _ ℂ
    Complex.instNormedAddCommGroup.toAddCommGroup
    instInnerProductSpaceRealComplex.toModule _ _ f f' x

/-- Explicit complex velocity `B_M` of the corrected C3 characteristic. -/
def c3CorrectedCharacteristicVelocity (cutoff : ℕ) (time : ℝ) : ℂ :=
  finiteBracketCharacteristicExponentDeriv 3 cutoff (nativeLine time) *
      Complex.I +
    c3OrientedBoundaryJetTimeDeriv cutoff time

/-- The explicit corrected complex velocity is the actual time derivative. -/
theorem c3CorrectedCharacteristic_hasDerivAt
    (cutoff : ℕ) (time : ℝ) :
    RealComplexHasDerivAt (c3CorrectedCharacteristic cutoff)
      (c3CorrectedCharacteristicVelocity cutoff time) time := by
  have hfiniteOuter :=
    finiteBracketCharacteristic_hasDerivAt (camera := 3) (by omega)
      cutoff (nativeLine time)
  have hfinite := hfiniteOuter.scomp time (nativeLine_hasDerivAt time)
  have hjet := c3OrientedBoundaryJet_nativeLine_hasDerivAt cutoff time
  have hsum := hfinite.add hjet
  have hsum' :
      RealComplexHasDerivAt
        ((finiteBracketCharacteristic 3 cutoff ∘ nativeLine) +
          fun u => c3OrientedBoundaryJet cutoff (nativeLine u))
        (c3CorrectedCharacteristicVelocity cutoff time) time := by
    apply hsum.congr_deriv
    simp only [c3CorrectedCharacteristicVelocity,
      c3OrientedBoundaryJetTimeDeriv, smul_eq_mul]
    ring
  apply hsum'.congr_of_eventuallyEq
  filter_upwards with u
  rfl

/-- Derivative form of the corrected complex velocity theorem. -/
theorem deriv_c3CorrectedCharacteristic (cutoff : ℕ) (time : ℝ) :
    deriv (c3CorrectedCharacteristic cutoff) time =
      c3CorrectedCharacteristicVelocity cutoff time :=
  (c3CorrectedCharacteristic_hasDerivAt cutoff time).deriv

/-- Real two-coordinate presentation of the corrected velocity `B_M`. -/
def c3CorrectedRealVelocity (cutoff : ℕ) (time : ℝ) :
    Operator.RealPlane :=
  unpackComplex (c3CorrectedCharacteristicVelocity cutoff time)

@[simp] theorem package_c3CorrectedRealVelocity
    (cutoff : ℕ) (time : ℝ) :
    CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
        (c3CorrectedRealVelocity cutoff time) =
      c3CorrectedCharacteristicVelocity cutoff time := by
  rfl

/-- The real corrected residual is exactly the unpacked complex chart. -/
theorem c3CorrectedRealResidual_eq_unpackComplex
    (cutoff : ℕ) (time : ℝ) :
    c3CorrectedRealResidual cutoff time =
      unpackComplex (c3CorrectedCharacteristic cutoff time) := by
  rw [← package_c3CorrectedRealResidual, unpackComplex_package]

/-- `B_M` is the genuine real derivative of the corrected resultant `A_M`. -/
theorem c3CorrectedRealResidual_hasDerivAt
    (cutoff : ℕ) (time : ℝ) :
    HasDerivAt (c3CorrectedRealResidual cutoff)
      (c3CorrectedRealVelocity cutoff time) time := by
  have hcomplex := c3CorrectedCharacteristic_hasDerivAt cutoff time
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt time hcomplex
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt time hcomplex
  have hpair := hre.prodMk him
  rw [show c3CorrectedRealResidual cutoff =
      fun u => unpackComplex (c3CorrectedCharacteristic cutoff u) by
    funext u
    exact c3CorrectedRealResidual_eq_unpackComplex cutoff u]
  change HasDerivAt
    (fun u =>
      ((c3CorrectedCharacteristic cutoff u).re,
        (c3CorrectedCharacteristic cutoff u).im))
    ((c3CorrectedCharacteristicVelocity cutoff time).re,
      (c3CorrectedCharacteristicVelocity cutoff time).im) time
  simpa only [Function.comp_apply, Complex.reCLM_apply,
    Complex.imCLM_apply] using hpair

/-- Corrected stationary numerator `h_M = A_M · B_M`. -/
def c3CorrectedStationaryNumerator (cutoff : ℕ) (time : ℝ) : ℝ :=
  Operator.realDot (c3CorrectedRealResidual cutoff time)
    (c3CorrectedRealVelocity cutoff time)

/-- The derivative of corrected quadratic energy is exactly `2 h_M`. -/
theorem deriv_c3CorrectedEnergy (cutoff : ℕ) (time : ℝ) :
    deriv
        (fun u => CPFormal.Analytic.Cp.nativeCarryRealPlaneEnergy
          (c3CorrectedRealResidual cutoff u)) time =
      2 * c3CorrectedStationaryNumerator cutoff time := by
  have hresidual := c3CorrectedRealResidual_hasDerivAt cutoff time
  have hx :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt
      time hresidual
  have hy :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt
      time hresidual
  have henergy := (hx.pow 2).add (hy.pow 2)
  have henergy' := henergy.congr_deriv
      (g' := 2 * c3CorrectedStationaryNumerator cutoff time) (by
    simp only [Function.comp_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    rw [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
    simp only [c3CorrectedStationaryNumerator, Operator.realDot]
    ring)
  rw [show
      (fun u => CPFormal.Analytic.Cp.nativeCarryRealPlaneEnergy
        (c3CorrectedRealResidual cutoff u)) =
        (⇑(ContinuousLinearMap.fst ℝ ℝ ℝ) ∘
              c3CorrectedRealResidual cutoff) ^ 2 +
          (⇑(ContinuousLinearMap.snd ℝ ℝ ℝ) ∘
              c3CorrectedRealResidual cutoff) ^ 2 by
    funext u
    rw [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
    rfl]
  exact henergy'.deriv

/-- A corrected stationary center is exactly a zero of `h_M`. -/
def IsC3CorrectedStationaryCenter (cutoff : ℕ) (time : ℝ) : Prop :=
  c3CorrectedStationaryNumerator cutoff time = 0

/-- Stationarity is equivalent to vanishing of the corrected energy derivative. -/
theorem isC3CorrectedStationaryCenter_iff_deriv_energy_eq_zero
    (cutoff : ℕ) (time : ℝ) :
    IsC3CorrectedStationaryCenter cutoff time ↔
      deriv
          (fun u => CPFormal.Analytic.Cp.nativeCarryRealPlaneEnergy
            (c3CorrectedRealResidual cutoff u)) time = 0 := by
  rw [deriv_c3CorrectedEnergy]
  simp [IsC3CorrectedStationaryCenter]

/--
At a corrected stationary center with nonzero velocity, the oriented
determinant is the remaining exact test for vanishing of the resultant.
-/
theorem c3CorrectedResidual_eq_zero_iff_realDet_eq_zero
    (cutoff : ℕ) (time : ℝ)
    (hvelocity : c3CorrectedRealVelocity cutoff time ≠ 0)
    (hstationary : IsC3CorrectedStationaryCenter cutoff time) :
    c3CorrectedRealResidual cutoff time = 0 ↔
      Operator.realDet (c3CorrectedRealResidual cutoff time)
        (c3CorrectedRealVelocity cutoff time) = 0 := by
  exact Operator.eq_zero_iff_realDet_eq_zero_of_realDot_eq_zero_of_right_ne_zero
    _ _ hvelocity hstationary

end

end NativeCarryC3Crosswalk
