import Mathlib.MeasureTheory.Measure.ResolventTransform
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

open scoped Topology

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Infinite
open MeasureTheory Measure
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
    rw [map_zero]
    change cameraEmbedding
      (Finsupp.single c3CauchyCamera 1) = 0 at hzero
    exact hzero
  have hcoordinate :=
    congrArg (fun u : CameraFinsupp => u c3CauchyCamera) hsingle
  simp at hcoordinate

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


/-! ## Finite spectral-measure certificate for off-axis analyticity -/

/-- The intrinsic height coordinate is the holomorphic affine map
`-I * (s - 1/2)`. -/
theorem c3BracketSpectralParameter_eq_affine (s : ℂ) :
    c3BracketSpectralParameter s =
      -Complex.I * (s - (1 / 2 : ℂ)) := by
  apply Complex.ext <;>
    simp [c3BracketSpectralParameter, carryComplexTimeOfParameter,
      criticalDisplacement]

/-- The intrinsic height coordinate is analytic everywhere. -/
theorem analyticAt_c3BracketSpectralParameter (s : ℂ) :
    AnalyticAt ℂ c3BracketSpectralParameter s := by
  have haffine :
      AnalyticAt ℂ
        (fun z : ℂ => -Complex.I * (z - (1 / 2 : ℂ))) s := by
    fun_prop
  exact haffine.congr
    (Filter.Eventually.of_forall fun z =>
      (c3BracketSpectralParameter_eq_affine z).symm)

/-- The resolvent transform of a finite real measure is analytic at every
nonreal parameter. -/
theorem analyticAt_resolventTransform_realMeasure_of_im_ne_zero
    (mu : Measure ℝ) [IsFiniteMeasure mu]
    {lambda : ℂ} (hlambda : lambda.im ≠ 0) :
    AnalyticAt ℂ (MeasureTheory.resolventTransform mu) lambda := by
  have hnot :
      lambda ∉ algebraMap ℝ ℂ '' mu.support := by
    rintro ⟨x, _hx, rfl⟩
    simp at hlambda
  have hopen :
      IsOpen (algebraMap ℝ ℂ '' mu.support)ᶜ := by
    apply isOpen_compl_iff.mpr
    refine
      (Topology.IsClosedEmbedding.isClosed_iff_image_isClosed ?_).mp
        Measure.isClosed_support
    exact (algebraMap_isometry ℝ ℂ).isClosedEmbedding
  exact
    (MeasureTheory.analyticOn_resolventTransform (μ := mu)).analyticAt
      (hopen.mem_nhds hnot)

/-- Composing a finite real spectral measure's resolvent transform with the
intrinsic height coordinate gives an analytic off-critical function.  The
minus sign matches the convention `(lambda - y)⁻¹` used by the native Cauchy
operator. -/
theorem analyticAt_neg_resolventTransform_comp_c3BracketSpectralParameter
    (mu : Measure ℝ) [IsFiniteMeasure mu]
    {s : ℂ} (hoff : s.re ≠ (1 : ℝ) / 2) :
    AnalyticAt ℂ
      (fun z : ℂ =>
        -MeasureTheory.resolventTransform mu
          (c3BracketSpectralParameter z)) s := by
  have hheight :
      (c3BracketSpectralParameter s).im ≠ 0 :=
    (c3BracketSpectralParameter_im_ne_zero_iff s).2 hoff
  have houter :
      AnalyticAt ℂ (MeasureTheory.resolventTransform mu)
        (c3BracketSpectralParameter s) :=
    analyticAt_resolventTransform_realMeasure_of_im_ne_zero mu hheight
  have hcomp :=
    houter.comp (analyticAt_c3BracketSpectralParameter s)
  exact hcomp.neg.congr
    (Filter.Eventually.of_forall fun z => by
      change
        -(MeasureTheory.resolventTransform mu
            (c3BracketSpectralParameter z)) =
          -MeasureTheory.resolventTransform mu
            (c3BracketSpectralParameter z)
      rfl)

/-- A finite spectral-measure representation of the already fixed C3 Cauchy
candidate.  This is representation data, not a new choice of logarithmic
derivative. -/
structure C3CauchyFiniteSpectralMeasureRepresentation where
  measure : Measure ℝ
  finiteMeasure : IsFiniteMeasure measure
  readout_eq_offCritical :
    ∀ {s : ℂ}, s.re ≠ (1 : ℝ) / 2 →
      c3BracketCauchyLogDerivativeCandidate s =
        -MeasureTheory.resolventTransform measure
          (c3BracketSpectralParameter s)

/-- The pointwise spectral-measure representation is an equality of germs at
every off-critical point. -/
theorem C3CauchyFiniteSpectralMeasureRepresentation.eventuallyEq_offCritical
    (model : C3CauchyFiniteSpectralMeasureRepresentation)
    {s : ℂ} (hoff : s.re ≠ (1 : ℝ) / 2) :
    c3BracketCauchyLogDerivativeCandidate =ᶠ[𝓝 s]
      fun z : ℂ =>
        -MeasureTheory.resolventTransform model.measure
          (c3BracketSpectralParameter z) := by
  rcases lt_or_gt_of_ne hoff with hleft | hright
  · have hopen :
        {z : ℂ | z.re < (1 : ℝ) / 2} ∈ 𝓝 s :=
      (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hleft
    filter_upwards [hopen] with z hz
    exact model.readout_eq_offCritical (by linarith)
  · have hopen :
        {z : ℂ | (1 : ℝ) / 2 < z.re} ∈ 𝓝 s :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hright
    filter_upwards [hopen] with z hz
    exact model.readout_eq_offCritical (by linarith)

/-- A finite spectral-measure representation discharges off-critical
analyticity of the concrete C3 Cauchy candidate. -/
theorem C3CauchyFiniteSpectralMeasureRepresentation.analyticAt_offCritical
    (model : C3CauchyFiniteSpectralMeasureRepresentation)
    {s : ℂ} (hoff : s.re ≠ (1 : ℝ) / 2) :
    AnalyticAt ℂ c3BracketCauchyLogDerivativeCandidate s := by
  letI : IsFiniteMeasure model.measure := model.finiteMeasure
  have hresolvent :=
    analyticAt_neg_resolventTransform_comp_c3BracketSpectralParameter
      model.measure hoff
  exact hresolvent.congr
    (model.eventuallyEq_offCritical hoff).symm

/-- The remaining arithmetic statement after the Cauchy candidate and its
spectral-measure regularity have been fixed. -/
def C3CauchyGenuineDifferentialIdentity : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    s.re ≠ (1 : ℝ) / 2 →
      deriv genuineContinuation =ᶠ[𝓝 s]
        -(c3BracketCauchyLogDerivativeCandidate * genuineContinuation)

/-- A finite spectral-measure representation plus the arithmetic differential
identity fills the concrete C3 identification. -/
theorem C3CauchyBracketLogDerivativeIdentification.ofSpectralMeasure
    (model : C3CauchyFiniteSpectralMeasureRepresentation)
    (hODE : C3CauchyGenuineDifferentialIdentity) :
    C3CauchyBracketLogDerivativeIdentification where
  analyticAt_offCritical := by
    intro s _hs hoff
    exact model.analyticAt_offCritical hoff
  differential_identity := hODE

/-- After the spectral-measure representation, the arithmetic differential
identity alone closes strong nonvanishing. -/
theorem genuineStrongNonvanishingInStrip_of_c3CauchySpectralMeasure_and_differentialIdentity
    (model : C3CauchyFiniteSpectralMeasureRepresentation)
    (hODE : C3CauchyGenuineDifferentialIdentity) :
    GenuineStrongNonvanishingInStrip :=
  genuineStrongNonvanishingInStrip_of_c3CauchyBracketIdentification
    (C3CauchyBracketLogDerivativeIdentification.ofSpectralMeasure
      model hODE)


/-! ## Canonical scalar spectral measure of the C3 camera -/

/-- Squared Kolmogorov mass carried by the canonical C3 Naimark vector. -/
def c3CauchyKolmogorovMass : NNReal :=
  ‖kolmogorovVector c3CauchyCamera‖₊ ^ 2

/-- Finite scalar measure before passage to logarithmic spectral
coordinates. -/
def c3CauchyBaseMeasure : Measure ℝ :=
  c3CauchyKolmogorovMass •
    positiveLebesgueMeasure.restrict
      (cameraInterval c3CauchyCamera)

noncomputable instance c3CauchyBaseMeasure_isFinite :
    IsFiniteMeasure c3CauchyBaseMeasure := by
  unfold c3CauchyBaseMeasure
  haveI :
      IsFiniteMeasure
        (positiveLebesgueMeasure.restrict
          (cameraInterval c3CauchyCamera)) :=
    (isFiniteMeasure_restrict).2
      (positiveLebesgueMeasure_cameraInterval_ne_top
        c3CauchyCamera)
  infer_instance

/-- Canonical C3 scalar spectral measure in the coordinate
`y = 1 + log x`. -/
def c3CauchySpectralMeasure : Measure ℝ :=
  c3CauchyBaseMeasure.map logarithmicCoordinate

noncomputable instance c3CauchySpectralMeasure_isFinite :
    IsFiniteMeasure c3CauchySpectralMeasure := by
  unfold c3CauchySpectralMeasure
  infer_instance

/-- The real C3 Cauchy quadratic form is the explicit interval integral of
the real scalar resolvent coefficient. -/
theorem c3CauchyRealQuadratic_eq_integral
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    inner ℝ c3CauchyCameraVector
        (allBasesCauchyRealPart lambda hlambda
          c3CauchyCameraVector) =
      ∫ x,
        (cameraInterval c3CauchyCamera).indicator
          (fun y =>
            logarithmicResolventRealCoefficient lambda y *
              (c3CauchyKolmogorovMass : ℝ)) x
        ∂positiveLebesgueMeasure := by
  rw [inner_allBasesCauchyRealPart]
  simp only [c3CauchyCameraVector,
    naimarkIsometry_cameraVector]
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [naimarkCameraVector_coeFn c3CauchyCamera,
      logarithmicResolventRealOperator_coeFn lambda hlambda
        (naimarkCameraVector c3CauchyCamera)] with x hvector hoperator
  rw [hvector, hoperator, hvector]
  by_cases hx : x ∈ cameraInterval c3CauchyCamera
  · simp [hx, c3CauchyKolmogorovMass,
      real_inner_smul_self_right, pow_two]
  · simp [hx]

/-- The imaginary C3 Cauchy quadratic form is the explicit interval integral
of the imaginary scalar resolvent coefficient. -/
theorem c3CauchyImaginaryQuadratic_eq_integral
    (lambda : ℂ) (hlambda : lambda.im ≠ 0) :
    inner ℝ c3CauchyCameraVector
        (allBasesCauchyImaginaryPart lambda hlambda
          c3CauchyCameraVector) =
      ∫ x,
        (cameraInterval c3CauchyCamera).indicator
          (fun y =>
            logarithmicResolventImaginaryCoefficient lambda y *
              (c3CauchyKolmogorovMass : ℝ)) x
        ∂positiveLebesgueMeasure := by
  rw [inner_allBasesCauchyImaginaryPart]
  simp only [c3CauchyCameraVector,
    naimarkIsometry_cameraVector]
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [naimarkCameraVector_coeFn c3CauchyCamera,
      logarithmicResolventImaginaryOperator_coeFn lambda hlambda
        (naimarkCameraVector c3CauchyCamera)] with x hvector hoperator
  rw [hvector, hoperator, hvector]
  by_cases hx : x ∈ cameraInterval c3CauchyCamera
  · simp [hx, c3CauchyKolmogorovMass,
      real_inner_smul_self_right, pow_two]
  · simp [hx]

end

end NativeCarryC3Crosswalk
