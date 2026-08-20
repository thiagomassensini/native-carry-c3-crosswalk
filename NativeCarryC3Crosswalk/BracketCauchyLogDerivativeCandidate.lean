import CPFormal.Analytic.CpNativeCarrySpectrumExhaustion
import NativeCarrySpectralWeyl.Infinite.Cauchy
import NativeCarryC3Crosswalk.BracketLogDerivativeConfinement

/-!
# Concrete C3 Cauchy candidate for the bracket logarithmic derivative

This module chooses actual data for the function field of
`RegularBracketLogDerivativeBridge`.

The complex carry-time coordinate sends the half-abscissa to the real height
axis.  Away from that axis, we compress the already constructed all-bases
Cauchy resolvent against the canonical camera-3 vector and combine its real
and imaginary quadratic forms into one complex scalar.

The resulting function is not a quotient by the Genuine continuation.  Its
strict transverse sign comes directly from the Cauchy operator:

* to the left of the half-abscissa its imaginary part is strictly negative;
* to the right it is strictly positive;
* hence it is nonzero at every off-critical point.

The remaining identification is stated with this concrete function fixed.  It
asks for off-axis analyticity and the arithmetic differential identity with
the Genuine continuation.  Supplying those two facts constructs the previous
bridge without choosing any further function.
-/

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Infinite
open Filter

noncomputable section

/-- The canonical all-bases camera index corresponding to C3. -/
def c3CauchyCamera : CameraIndex :=
  ⟨3, by norm_num⟩

/-- Canonical camera-3 vector in the completed all-bases camera Hilbert space. -/
def c3CauchyCameraVector : CameraHilbert :=
  cameraVector c3CauchyCamera

/-- The canonical C3 camera vector is nonzero. -/
theorem c3CauchyCameraVector_ne_zero :
    c3CauchyCameraVector ≠ 0 := by
  intro hzero
  have hsingle :
      (Finsupp.single c3CauchyCamera 1 : CameraFinsupp) = 0 := by
    apply cameraEmbedding.injective
    simpa [c3CauchyCameraVector, cameraVector] using hzero
  have hcoordinate :=
    congrArg (fun u : CameraFinsupp => u c3CauchyCamera) hsingle
  simpa using hcoordinate

/-- Scalar Cauchy readout at a nonreal height parameter. -/
def c3CauchyScalarAt (lambda : ℂ) (hlambda : lambda.im ≠ 0) : ℂ :=
  ((inner ℝ c3CauchyCameraVector
      (allBasesCauchyRealPart lambda hlambda c3CauchyCameraVector) : ℝ) : ℂ) +
    ((inner ℝ c3CauchyCameraVector
      (allBasesCauchyImaginaryPart lambda hlambda c3CauchyCameraVector) : ℝ) : ℂ) *
      Complex.I

/-- Totalized scalar Cauchy readout.  Only its values off the real height axis
are used below. -/
def c3CauchyScalarReadout (lambda : ℂ) : ℂ :=
  if hlambda : lambda.im ≠ 0 then
    c3CauchyScalarAt lambda hlambda
  else
    0

/-- Off the real height axis, totalization recovers the compressed Cauchy
quadratic form. -/
theorem c3CauchyScalarReadout_eq
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    c3CauchyScalarReadout lambda =
      c3CauchyScalarAt lambda hlambda := by
  simp [c3CauchyScalarReadout, hlambda]

/-- The imaginary part of the scalar readout is exactly the imaginary Cauchy
quadratic form. -/
theorem c3CauchyScalarReadout_im
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    (c3CauchyScalarReadout lambda).im =
      inner ℝ c3CauchyCameraVector
        (allBasesCauchyImaginaryPart lambda hlambda
          c3CauchyCameraVector) := by
  rw [c3CauchyScalarReadout_eq lambda hlambda]
  simp [c3CauchyScalarAt]

/-- Strict anti-Herglotz sign in the upper height half-plane. -/
theorem c3CauchyScalarReadout_im_neg
    {lambda : ℂ} (hlambda : 0 < lambda.im) :
    (c3CauchyScalarReadout lambda).im < 0 := by
  rw [c3CauchyScalarReadout_im lambda hlambda.ne']
  exact allBasesCauchyImaginaryPart_inner_neg
    hlambda c3CauchyCameraVector_ne_zero

/-- Strict reversed sign in the lower height half-plane. -/
theorem c3CauchyScalarReadout_im_pos
    {lambda : ℂ} (hlambda : lambda.im < 0) :
    0 < (c3CauchyScalarReadout lambda).im := by
  rw [c3CauchyScalarReadout_im lambda hlambda.ne]
  exact allBasesCauchyImaginaryPart_inner_pos
    hlambda c3CauchyCameraVector_ne_zero

/-- The intrinsic complex carry time is the spectral height parameter for the
C3 Cauchy candidate. -/
def c3BracketSpectralParameter (s : ℂ) : ℂ :=
  carryComplexTimeOfParameter s

@[simp] theorem c3BracketSpectralParameter_im (s : ℂ) :
    (c3BracketSpectralParameter s).im =
      -criticalDisplacement s.re := by
  simp [c3BracketSpectralParameter]

/-- The spectral height is off the real axis exactly away from the
half-abscissa. -/
theorem c3BracketSpectralParameter_im_ne_zero_iff (s : ℂ) :
    (c3BracketSpectralParameter s).im ≠ 0 ↔
      s.re ≠ (1 : ℝ) / 2 := by
  rw [c3BracketSpectralParameter_im]
  unfold criticalDisplacement
  constructor <;> intro h
  · intro hre
    apply h
    rw [hre]
    ring
  · intro him
    apply h
    linarith

/-- Concrete bracket-log-derivative candidate obtained from the canonical C3
Cauchy scalar in the intrinsic height coordinate. -/
def c3BracketCauchyLogDerivativeCandidate (s : ℂ) : ℂ :=
  c3CauchyScalarReadout (c3BracketSpectralParameter s)

/-- Left of the half-abscissa, the candidate has strictly negative imaginary
part. -/
theorem c3BracketCauchyLogDerivativeCandidate_im_neg_of_re_lt_half
    {s : ℂ} (hs : s.re < (1 : ℝ) / 2) :
    (c3BracketCauchyLogDerivativeCandidate s).im < 0 := by
  have hheight : 0 < (c3BracketSpectralParameter s).im := by
    rw [c3BracketSpectralParameter_im]
    unfold criticalDisplacement
    linarith
  simpa [c3BracketCauchyLogDerivativeCandidate] using
    c3CauchyScalarReadout_im_neg hheight

/-- Right of the half-abscissa, the candidate has strictly positive imaginary
part. -/
theorem c3BracketCauchyLogDerivativeCandidate_im_pos_of_half_lt_re
    {s : ℂ} (hs : (1 : ℝ) / 2 < s.re) :
    0 < (c3BracketCauchyLogDerivativeCandidate s).im := by
  have hheight : (c3BracketSpectralParameter s).im < 0 := by
    rw [c3BracketSpectralParameter_im]
    unfold criticalDisplacement
    linarith
  simpa [c3BracketCauchyLogDerivativeCandidate] using
    c3CauchyScalarReadout_im_pos hheight

/-- The concrete Cauchy candidate never vanishes away from the
half-abscissa. -/
theorem c3BracketCauchyLogDerivativeCandidate_ne_zero_of_re_ne_half
    {s : ℂ} (hoff : s.re ≠ (1 : ℝ) / 2) :
    c3BracketCauchyLogDerivativeCandidate s ≠ 0 := by
  intro hzero
  have himzero :
      (c3BracketCauchyLogDerivativeCandidate s).im = 0 := by
    rw [hzero]
    rfl
  by_cases hleft : s.re < (1 : ℝ) / 2
  · have hneg :=
      c3BracketCauchyLogDerivativeCandidate_im_neg_of_re_lt_half hleft
    linarith
  · have hright : (1 : ℝ) / 2 < s.re := by
      exact lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm hoff)
    have hpos :=
      c3BracketCauchyLogDerivativeCandidate_im_pos_of_half_lt_re hright
    linarith

/-- Exact remaining identification for the concrete C3 Cauchy candidate.

The function is no longer a field of the structure: it has been fixed above
from the canonical C3 camera and the all-bases resolvent.  The two fields are
the operator-analytic regularity and the arithmetic log-jet identity that must
be established for that fixed readout. -/
structure C3CauchyBracketLogDerivativeIdentification : Prop where
  analyticAt_offCritical :
    ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
      s.re ≠ (1 : ℝ) / 2 →
        AnalyticAt ℂ c3BracketCauchyLogDerivativeCandidate s
  differential_identity :
    ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
      s.re ≠ (1 : ℝ) / 2 →
        deriv genuineContinuation =ᶠ[𝓝 s]
          -(c3BracketCauchyLogDerivativeCandidate * genuineContinuation)

/-- The concrete C3 Cauchy identification instantiates the general regular
bracket log-derivative bridge. -/
def C3CauchyBracketLogDerivativeIdentification.toRegularBridge
    (identification : C3CauchyBracketLogDerivativeIdentification) :
    RegularBracketLogDerivativeBridge where
  logarithmicDerivative := c3BracketCauchyLogDerivativeCandidate
  analyticAt_offCritical :=
    identification.analyticAt_offCritical
  differential_identity :=
    identification.differential_identity

/-- Once the concrete C3 Cauchy identification is supplied, every Genuine zero
in the open strip lies on the half-abscissa. -/
theorem genuineZero_re_eq_half_of_c3CauchyBracketIdentification
    (identification : C3CauchyBracketLogDerivativeIdentification)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    s.re = (1 : ℝ) / 2 :=
  genuineZero_re_eq_half_of_regularBracketLogDerivative
    identification.toRegularBridge hs hzero

/-- Global strong nonvanishing obtained from the fixed C3 Cauchy candidate. -/
theorem genuineStrongNonvanishingInStrip_of_c3CauchyBracketIdentification
    (identification : C3CauchyBracketLogDerivativeIdentification) :
    GenuineStrongNonvanishingInStrip :=
  genuineStrongNonvanishingInStrip_of_regularBracketLogDerivative
    identification.toRegularBridge

/-- The same concrete identification closes the global relational bracket
law. -/
theorem genuineZerosCloseC3GenuineBracketGreenForm_of_c3CauchyBracketIdentification
    (identification : C3CauchyBracketLogDerivativeIdentification) :
    GenuineZerosCloseC3GenuineBracketGreenForm :=
  genuineZerosCloseC3GenuineBracketGreenForm_of_regularBracketLogDerivative
    identification.toRegularBridge

end

end NativeCarryC3Crosswalk
