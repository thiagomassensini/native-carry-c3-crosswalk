import NativeCarryC3Crosswalk.C3Stationary
import NativeCarryC3Crosswalk.C3SecondDerivativeCore

/-!
# Corrected C3 acceleration and stationary slope

This module materializes the second corrected time derivative required by the
stationary-localization certificate and proves the exact formula

`h_M' = B_M · B_M + A_M · A_M''`.
-/

namespace NativeCarryC3Crosswalk

open FiniteNativeCarryOperator
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-- Explicit complex acceleration of the corrected C3 characteristic. -/
def c3CorrectedCharacteristicAcceleration
    (cutoff : ℕ) (time : ℝ) : ℂ :=
  finiteBracketCharacteristicExponentSecondDeriv 3 cutoff (nativeLine time) *
      Complex.I * Complex.I +
    c3OrientedBoundaryJetTimeSecondDeriv cutoff time

/-- The corrected complex acceleration is the derivative of the velocity. -/
theorem c3CorrectedCharacteristicVelocity_hasDerivAt
    (cutoff : ℕ) (time : ℝ) :
    RealComplexHasDerivAt (c3CorrectedCharacteristicVelocity cutoff)
      (c3CorrectedCharacteristicAcceleration cutoff time) time := by
  have hfiniteOuter :=
    finiteBracketCharacteristicExponentDeriv_hasDerivAt
      (camera := 3) (by omega) cutoff (nativeLine time)
  have hfiniteLine := hfiniteOuter.scomp time (nativeLine_hasDerivAt time)
  have hfinite := hfiniteLine.mul_const Complex.I
  have hjet := c3OrientedBoundaryJetTimeDeriv_hasDerivAt cutoff time
  have hsum := hfinite.add hjet
  have hsum' :
      RealComplexHasDerivAt
        ((fun u =>
            finiteBracketCharacteristicExponentDeriv 3 cutoff
              (nativeLine u) * Complex.I) +
          c3OrientedBoundaryJetTimeDeriv cutoff)
        (c3CorrectedCharacteristicAcceleration cutoff time) time := by
    apply hsum.congr_deriv
    simp only [c3CorrectedCharacteristicAcceleration, smul_eq_mul]
    ring
  apply hsum'.congr_of_eventuallyEq
  filter_upwards with u
  rfl

/-- Derivative form of the corrected complex acceleration theorem. -/
theorem deriv_c3CorrectedCharacteristicVelocity
    (cutoff : ℕ) (time : ℝ) :
    deriv (c3CorrectedCharacteristicVelocity cutoff) time =
      c3CorrectedCharacteristicAcceleration cutoff time :=
  (c3CorrectedCharacteristicVelocity_hasDerivAt cutoff time).deriv

/-- Real two-coordinate presentation of the corrected acceleration `A_M''`. -/
def c3CorrectedRealAcceleration (cutoff : ℕ) (time : ℝ) :
    Operator.RealPlane :=
  unpackComplex (c3CorrectedCharacteristicAcceleration cutoff time)

@[simp] theorem package_c3CorrectedRealAcceleration
    (cutoff : ℕ) (time : ℝ) :
    CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
        (c3CorrectedRealAcceleration cutoff time) =
      c3CorrectedCharacteristicAcceleration cutoff time := by
  rfl

/-- The corrected acceleration is the genuine real derivative of `B_M`. -/
theorem c3CorrectedRealVelocity_hasDerivAt
    (cutoff : ℕ) (time : ℝ) :
    HasDerivAt (c3CorrectedRealVelocity cutoff)
      (c3CorrectedRealAcceleration cutoff time) time := by
  have hcomplex :=
    c3CorrectedCharacteristicVelocity_hasDerivAt cutoff time
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt time hcomplex
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt time hcomplex
  have hpair := hre.prodMk him
  change HasDerivAt
    (fun u =>
      ((c3CorrectedCharacteristicVelocity cutoff u).re,
        (c3CorrectedCharacteristicVelocity cutoff u).im))
    ((c3CorrectedCharacteristicAcceleration cutoff time).re,
      (c3CorrectedCharacteristicAcceleration cutoff time).im) time
  simpa only [Function.comp_apply, Complex.reCLM_apply,
    Complex.imCLM_apply] using hpair

/-- Explicit derivative of the stationary numerator. -/
def c3CorrectedStationarySlope (cutoff : ℕ) (time : ℝ) : ℝ :=
  Operator.realDot (c3CorrectedRealVelocity cutoff time)
      (c3CorrectedRealVelocity cutoff time) +
    Operator.realDot (c3CorrectedRealResidual cutoff time)
      (c3CorrectedRealAcceleration cutoff time)

/-- The stationary slope is exactly the derivative of `h_M`. -/
theorem deriv_c3CorrectedStationaryNumerator
    (cutoff : ℕ) (time : ℝ) :
    deriv (c3CorrectedStationaryNumerator cutoff) time =
      c3CorrectedStationarySlope cutoff time := by
  have hresidual := c3CorrectedRealResidual_hasDerivAt cutoff time
  have hvelocity := c3CorrectedRealVelocity_hasDerivAt cutoff time
  have hax :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt
      time hresidual
  have hay :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt
      time hresidual
  have hbx :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt
      time hvelocity
  have hby :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt
      time hvelocity
  have hdot := (hax.mul hbx).add (hay.mul hby)
  have hdot' := hdot.congr_deriv
      (g' := c3CorrectedStationarySlope cutoff time) (by
    simp only [Function.comp_apply]
    rw [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
    simp only [c3CorrectedStationarySlope, Operator.realDot]
    ring)
  rw [show c3CorrectedStationaryNumerator cutoff =
      (⇑(ContinuousLinearMap.fst ℝ ℝ ℝ) ∘
            c3CorrectedRealResidual cutoff) *
          (⇑(ContinuousLinearMap.fst ℝ ℝ ℝ) ∘
            c3CorrectedRealVelocity cutoff) +
        (⇑(ContinuousLinearMap.snd ℝ ℝ ℝ) ∘
            c3CorrectedRealResidual cutoff) *
          (⇑(ContinuousLinearMap.snd ℝ ℝ ℝ) ∘
            c3CorrectedRealVelocity cutoff) by
    funext u
    rw [ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
    rfl]
  exact hdot'.deriv

/-- The concrete stationary numerator is continuous on the real line. -/
theorem continuous_c3CorrectedStationaryNumerator (cutoff : ℕ) :
    Continuous (c3CorrectedStationaryNumerator cutoff) := by
  have hresidual : Continuous (c3CorrectedRealResidual cutoff) :=
    continuous_iff_continuousAt.mpr fun time =>
      (c3CorrectedRealResidual_hasDerivAt cutoff time).continuousAt
  have hvelocity : Continuous (c3CorrectedRealVelocity cutoff) :=
    continuous_iff_continuousAt.mpr fun time =>
      (c3CorrectedRealVelocity_hasDerivAt cutoff time).continuousAt
  unfold c3CorrectedStationaryNumerator Operator.realDot
  exact (((continuous_fst.comp hresidual).mul
      (continuous_fst.comp hvelocity)).add
    ((continuous_snd.comp hresidual).mul
      (continuous_snd.comp hvelocity)))

end

end NativeCarryC3Crosswalk
