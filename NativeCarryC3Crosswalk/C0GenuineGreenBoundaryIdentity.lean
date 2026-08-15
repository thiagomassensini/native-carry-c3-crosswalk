import NativeCarryC3Crosswalk.GenuineBracketGreenFactorization
import NativeCarryC3Crosswalk.ArithmeticNonlocalTrace
import CPFormal.Analytic.CpPairedGenuineBridgeTarget

/-!
# C0 Genuine readout versus the reflected Green boundary form

The historical C2 vertical factor `C0` is the nowhere-vanishing factor called
`pairedBridgeFactor` in the pinned `CPFormal` API.  This module transports that
readout to the canonical C3 angular port and asks, before any zero is imposed,
whether its reflected quadratic pairing is the Green form.

There is an exact universal identity, but it contains the complete angular
provenance correction:

`radial * C0Pairing = dressing * (GreenForm + radial * correction)`.

Thus `C0` does not disappear and no confinement statement is assumed.  Since
the dressing is nonzero in the open Genuine strip, deleting the correction is
equivalent to proving that the scaled correction itself vanishes.  The latter
is therefore not obtained from nonvanishing of `C0`.
-/

open scoped Topology

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary
open Filter

noncomputable section

/-- The historical C2 factor `C0`, using its canonical native definition in
the pinned `CPFormal` package. -/
def c0VerticalFactor (s : ℂ) : ℂ :=
  pairedBridgeFactor s

/-- `C0` is nonzero throughout the open Genuine strip. -/
theorem c0VerticalFactor_ne_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    c0VerticalFactor s ≠ 0 := by
  exact pairedBridgeFactor_ne_zero hs

/-- Change of camera from the canonical C3 bracket factor to the C2 `C0`
factor.  Both numerator and denominator are independently nonzero in the
open strip. -/
def c0ToC3BoundaryDressing (s : ℂ) : ℂ :=
  c0VerticalFactor s / cpChartFactor 3 s

/-- The C2-to-C3 boundary dressing never vanishes in the open strip. -/
theorem c0ToC3BoundaryDressing_ne_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    c0ToC3BoundaryDressing s ≠ 0 := by
  exact div_ne_zero (c0VerticalFactor_ne_zero hs)
    (cpChartFactor_ne_zero_on_genuineCriticalStrip 3 (by norm_num) hs)

/-- Finite C3 angular trace dressed so that its limit is the historical C2
central Genuine numerator `C0(s) * Genuine(s)`. -/
def finiteC0GenuineBoundaryTrace (M : ℕ) (s : ℂ) : ℂ :=
  c0ToC3BoundaryDressing s * finiteCanonicalAngularTrace M s

/-- The dressed finite trace converges exactly to the C2 central Genuine
continuation.  No vanishing or critical-line hypothesis is used. -/
theorem finiteC0GenuineBoundaryTrace_tendsto
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Tendsto (fun M : ℕ ↦ finiteC0GenuineBoundaryTrace M s)
      atTop (nhds (genuineCentralContinuationC2 s)) := by
  have htrace := finiteCanonicalAngularTrace_tendsto
    (s := s) (by linarith [hs.1])
  have hscaled :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ ↦ c0ToC3BoundaryDressing s) atTop
        (nhds (c0ToC3BoundaryDressing s))).mul htrace
  have htarget :
      c0ToC3BoundaryDressing s * bracketedDirichletChart 3 s =
        genuineCentralContinuationC2 s := by
    rw [bracketedDirichletChart_eq_cpChartFactor_mul_genuineContinuation
      3 (by norm_num) (by norm_num) hs,
      genuineCentralContinuationC2_eq hs]
    unfold c0ToC3BoundaryDressing c0VerticalFactor
    field_simp [cpChartFactor_ne_zero_on_genuineCriticalStrip
      3 (by norm_num) hs]
  rw [← htarget]
  simpa only [finiteC0GenuineBoundaryTrace] using hscaled

/-- Reflected quadratic pairing of the two C0-dressed finite boundary
traces.  A bilinear Green form must be compared with this reflected product,
not with one linear scalar readout. -/
def finiteC0GenuineBoundaryPairing (M : ℕ) (s : ℂ) : ℂ :=
  (starRingEnd ℂ) (finiteC0GenuineBoundaryTrace M s) *
    finiteC0GenuineBoundaryTrace M (reflectedParameter s)

/-- The reflected C0 boundary pairing converges to the product of the two C2
central Genuine continuations, without assuming either factor vanishes. -/
theorem finiteC0GenuineBoundaryPairing_tendsto
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Tendsto (fun M : ℕ ↦ finiteC0GenuineBoundaryPairing M s)
      atTop
      (nhds
        ((starRingEnd ℂ) (genuineCentralContinuationC2 s) *
          genuineCentralContinuationC2 (reflectedParameter s))) := by
  have hdirect := finiteC0GenuineBoundaryTrace_tendsto hs
  have hreflected := finiteC0GenuineBoundaryTrace_tendsto
    (reflectedParameter_mem_genuineCriticalStrip hs)
  have hconj :
      Tendsto
        (fun M : ℕ ↦
          (starRingEnd ℂ) (finiteC0GenuineBoundaryTrace M s))
        atTop (nhds ((starRingEnd ℂ) (genuineCentralContinuationC2 s))) := by
    simpa [Function.comp_def] using
      (Complex.continuous_conj.tendsto
        (genuineCentralContinuationC2 s)).comp hdirect
  simpa only [finiteC0GenuineBoundaryPairing] using hconj.mul hreflected

/-- The exact universal angular ledger after radial scaling.  It is the
strongest Green identity supplied by the current bracket carrier before any
zero or limiting hypothesis: the provenance correction remains explicit. -/
theorem radialScaledAngularScalarPairing_eq_greenForm_add_correction
    (M : ℕ) (s : ℂ) :
    ((cpRadialDifference 3 (criticalDisplacement s.re) : ℝ) : ℂ) *
        finiteCanonicalAngularScalarPairing M s =
      greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M) (reflectedParameter s)) +
        ((cpRadialDifference 3
          (criticalDisplacement s.re) : ℝ) : ℂ) *
          finiteCanonicalAngularGreenCorrection M s := by
  rw [finiteCanonicalAngularScalarPairing_eq_green_add_correction,
    greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_radialFactorization]
  ring

/-- Exact C0-dressed Genuine/Green identity for every finite cutoff and every
complex parameter.  This is an identity before zeros.  The right side shows
precisely which provenance term prevents a pure scalar-readout factorization. -/
theorem radialScaledC0GenuineBoundaryPairing_eq_dressedGreen_add_correction
    (M : ℕ) (s : ℂ) :
    ((cpRadialDifference 3 (criticalDisplacement s.re) : ℝ) : ℂ) *
        finiteC0GenuineBoundaryPairing M s =
      ((starRingEnd ℂ) (c0ToC3BoundaryDressing s) *
          c0ToC3BoundaryDressing (reflectedParameter s)) *
        (greenForm (𝕜 := ℂ)
            (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
            (finiteC3GenuineBracketGreenBoundaryPair
              (3 * M) (reflectedParameter s)) +
          ((cpRadialDifference 3
            (criticalDisplacement s.re) : ℝ) : ℂ) *
            finiteCanonicalAngularGreenCorrection M s) := by
  unfold finiteC0GenuineBoundaryPairing finiteC0GenuineBoundaryTrace
  simp only [map_mul]
  calc
    ((cpRadialDifference 3
        (criticalDisplacement s.re) : ℝ) : ℂ) *
          (((starRingEnd ℂ) (c0ToC3BoundaryDressing s) *
              (starRingEnd ℂ) (finiteCanonicalAngularTrace M s)) *
            (c0ToC3BoundaryDressing (reflectedParameter s) *
              finiteCanonicalAngularTrace M (reflectedParameter s))) =
        ((starRingEnd ℂ) (c0ToC3BoundaryDressing s) *
            c0ToC3BoundaryDressing (reflectedParameter s)) *
          (((cpRadialDifference 3
              (criticalDisplacement s.re) : ℝ) : ℂ) *
            finiteCanonicalAngularScalarPairing M s) := by
              rw [finiteCanonicalAngularScalarPairing_eq_product]
              ring
    _ = ((starRingEnd ℂ) (c0ToC3BoundaryDressing s) *
            c0ToC3BoundaryDressing (reflectedParameter s)) *
          (greenForm (𝕜 := ℂ)
              (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
              (finiteC3GenuineBracketGreenBoundaryPair
                (3 * M) (reflectedParameter s)) +
            ((cpRadialDifference 3
              (criticalDisplacement s.re) : ℝ) : ℂ) *
              finiteCanonicalAngularGreenCorrection M s) := by
                rw [radialScaledAngularScalarPairing_eq_greenForm_add_correction]

/-- Since both C0 camera dressings are nonzero in the strip, replacing the
exact corrected ledger by a pure Green equality is equivalent to annihilating
the scaled angular correction.  No zero assumption occurs in either side. -/
theorem radialScaledC0GenuineBoundaryPairing_eq_pureGreen_iff_correction_eq_zero
    (M : ℕ) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    (((cpRadialDifference 3 (criticalDisplacement s.re) : ℝ) : ℂ) *
        finiteC0GenuineBoundaryPairing M s =
      ((starRingEnd ℂ) (c0ToC3BoundaryDressing s) *
          c0ToC3BoundaryDressing (reflectedParameter s)) *
        greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M) (reflectedParameter s))) ↔
      ((cpRadialDifference 3
        (criticalDisplacement s.re) : ℝ) : ℂ) *
          finiteCanonicalAngularGreenCorrection M s = 0 := by
  rw [radialScaledC0GenuineBoundaryPairing_eq_dressedGreen_add_correction]
  let d : ℂ :=
    (starRingEnd ℂ) (c0ToC3BoundaryDressing s) *
      c0ToC3BoundaryDressing (reflectedParameter s)
  have hdirect : c0ToC3BoundaryDressing s ≠ 0 :=
    c0ToC3BoundaryDressing_ne_zero hs
  have hreflected :
      c0ToC3BoundaryDressing (reflectedParameter s) ≠ 0 :=
    c0ToC3BoundaryDressing_ne_zero
      (reflectedParameter_mem_genuineCriticalStrip hs)
  have hconj :
      (starRingEnd ℂ) (c0ToC3BoundaryDressing s) ≠ 0 := by
    intro hzero
    apply hdirect
    have := congrArg (starRingEnd ℂ) hzero
    simpa using this
  have hd : d ≠ 0 := mul_ne_zero hconj hreflected
  change
    d *
        (greenForm (𝕜 := ℂ)
            (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
            (finiteC3GenuineBracketGreenBoundaryPair
              (3 * M) (reflectedParameter s)) +
          ((cpRadialDifference 3
            (criticalDisplacement s.re) : ℝ) : ℂ) *
            finiteCanonicalAngularGreenCorrection M s) =
        d *
          greenForm (𝕜 := ℂ)
            (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
            (finiteC3GenuineBracketGreenBoundaryPair
              (3 * M) (reflectedParameter s)) ↔
      ((cpRadialDifference 3
        (criticalDisplacement s.re) : ℝ) : ℂ) *
          finiteCanonicalAngularGreenCorrection M s = 0
  constructor
  · intro h
    apply (mul_eq_zero.mp ?_).resolve_left hd
    linear_combination h
  · intro h
    rw [h, add_zero]

/-! ## Finite coarse-readout obstruction with C0 included -/

/-- Dress the two coarse scalar boundary coordinates by the direct and
reflected C0 factors. -/
def finiteC0GenuineCoarseDressing (s : ℂ) :
    (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) where
  toFun x :=
    (c0VerticalFactor s * x.1,
      c0VerticalFactor (reflectedParameter s) * x.2)
  map_add' x y := by
    apply Prod.ext <;> simp [mul_add]
  map_smul' c x := by
    apply Prod.ext <;> simp [mul_left_comm]

/-- The finite C0 Genuine readout still performs scalar synthesis before its
nonzero vertical dressing. -/
def finiteC0GenuineCoarseReadout (M : ℕ) (s : ℂ) :
    FiniteC3GreenPortCarrier M →ₗ[ℂ] (ℂ × ℂ) :=
  (finiteC0GenuineCoarseDressing s).comp
    (finiteC3CoarseBoundaryReadout M)

@[simp] theorem finiteC0GenuineCoarseReadout_apply
    (M : ℕ) (s : ℂ) (x : FiniteC3GreenPortCarrier M) :
    finiteC0GenuineCoarseReadout M s x =
      (c0VerticalFactor s * finiteC3VectorSynthesis M x.1,
        c0VerticalFactor (reflectedParameter s) *
          finiteC3VectorSynthesis M x.2) :=
  rfl

/-- Including the nowhere-vanishing C0 factor cannot make a two-scalar
Genuine readout detect the fixed diagonal Green relation.  The same explicit
two-cell provenance witness is killed before C0 is applied.  This obstruction
uses neither a zero nor any assertion about the critical line. -/
theorem no_finiteC3_boundaryDefect_factorization_through_c0GenuineReadout
    {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
    (s : ℂ)
    (boundaryDefect : FiniteC3GreenPortCarrier 2 →ₗ[ℂ] Z)
    (transport : (ℂ × ℂ) →ₗ[ℂ] Z)
    (hfactor : boundaryDefect =
      transport.comp (finiteC0GenuineCoarseReadout 2 s))
    (hdetect : ∀ x,
      boundaryDefect x = 0 ↔ x ∈ finiteC3DiagonalGreenRelation 2) :
    False := by
  have hreadout :
      finiteC0GenuineCoarseReadout 2 s finiteC3CoarseKernelWitness = 0 := by
    rw [finiteC0GenuineCoarseReadout, LinearMap.comp_apply,
      finiteC3CoarseBoundaryReadout_kernelWitness,
      map_zero]
  have hdefect : boundaryDefect finiteC3CoarseKernelWitness = 0 := by
    rw [hfactor, LinearMap.comp_apply, hreadout, map_zero]
  exact finiteC3CoarseKernelWitness_not_mem_diagonal
    ((hdetect finiteC3CoarseKernelWitness).1 hdefect)

end

end NativeCarryC3Crosswalk
