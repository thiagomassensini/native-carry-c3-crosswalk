import NativeCarryC3Crosswalk.GenuineBracketGreenIdentity
import CPFormal.Analytic.CpGenuineFirstMultibaseCutoff

/-!
# Nonlocal Genuine-tail transport into the C3 Green language

A Genuine zero is not represented here by an arbitrary vector in the kernel of
one finite scalar synthesis.  Its finite bracket chart is tied, at every
cutoff, to the uniquely determined tail of the same summable bracket series.

This module transports that head--tail coherence to the already constructed C3
Green boundary pair.  The enriched finite defect retains

* the bracket-resolved Green form;
* the moving reflected outer endpoint; and
* the unresolved nonlocal bracket tail.

For every cutoff, before assuming a zero, Lean proves

`tailGreenDefect = -chartFactor 3 s * genuineContinuation s`.

Consequently its kernel is exactly the Genuine kernel on the open strip.  This
is a transport of the scalar kernel into a nonlocal Green ledger; it does not
assert that the pure Green form vanishes and therefore does not assume or prove
critical-line confinement.
-/

open scoped Topology

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary
open Filter

noncomputable section

/-- The nonlocal boundary correction retained by the C3 Green ledger: the
moving reflected endpoint plus the exact unresolved tail of the bracket
series. -/
def finiteC3GenuineTailGreenBoundary (M : ℕ) (s : ℂ) : ℂ :=
  finiteReflectedOuterEndpoint (3 * M) s +
    realCpBracketCutoffTail 3 M s

/-- The Green defect enriched by the canonical Genuine tail.  Unlike the
coarse two-scalar readout, this definition does not discard the part of the
infinite bracket series lying beyond the cutoff. -/
def finiteC3GenuineTailGreenDefect (M : ℕ) (s : ℂ) : ℂ :=
  finiteCanonicalTfvdCoupledGenuineGreenFlux 3 M s -
    (greenForm (𝕜 := ℂ)
        (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
        (finiteC3GenuineBracketGreenBoundaryPair
          (3 * M) (reflectedParameter s)) +
      finiteC3GenuineTailGreenBoundary M s)

/-- Exact finite sum check, with no convergence or strip hypothesis: the
tail-coherent Green defect is the negative of `finite chart + unresolved
tail`.  This records the sign and both summands explicitly. -/
theorem finiteC3GenuineTailGreenDefect_eq_neg_finiteChart_add_tail
    (M : ℕ) (s : ℂ) :
    finiteC3GenuineTailGreenDefect M s =
      -(finiteBracketedDirichletChart 3 M s +
        realCpBracketCutoffTail 3 M s) := by
  unfold finiteC3GenuineTailGreenDefect finiteC3GenuineTailGreenBoundary
  rw [finiteC3BracketCoupledGenuineGreenFlux_eq_greenForm_add_outer_sub_chart]
  ring

/-- Universal head--tail Green identity.  The enriched defect is exactly the
negative infinite C3 bracket chart at every cutoff. -/
theorem finiteC3GenuineTailGreenDefect_eq_neg_chart
    (M : ℕ) {s : ℂ} (hs : -1 < s.re) :
    finiteC3GenuineTailGreenDefect M s =
      -bracketedDirichletChart 3 s := by
  rw [finiteC3GenuineTailGreenDefect_eq_neg_finiteChart_add_tail,
    bracketedDirichletChart_eq_finite_add_cutoffTail
      3 M (by norm_num) hs]

/-- Projective coherence in Green language: after retaining the canonical
tail, the defect is independent of the chosen finite cutoff. -/
theorem finiteC3GenuineTailGreenDefect_cutoff_invariant
    (M N : ℕ) {s : ℂ} (hs : -1 < s.re) :
    finiteC3GenuineTailGreenDefect M s =
      finiteC3GenuineTailGreenDefect N s := by
  rw [finiteC3GenuineTailGreenDefect_eq_neg_chart M hs,
    finiteC3GenuineTailGreenDefect_eq_neg_chart N hs]

/-- On the open Genuine strip, the same universal defect factors through the
single Genuine readout and the independently nonvanishing C3 chart factor. -/
theorem finiteC3GenuineTailGreenDefect_eq_neg_factor_mul_genuine
    (M : ℕ) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    finiteC3GenuineTailGreenDefect M s =
      -(cpChartFactor 3 s * genuineContinuation s) := by
  rw [finiteC3GenuineTailGreenDefect_eq_neg_chart M (by linarith [hs.1]),
    bracketedDirichletChart_eq_cpChartFactor_mul_genuineContinuation
      3 (by norm_num) (by norm_num) hs]

/-- Exact kernel transport: at any finite cutoff the nonlocal Green defect
vanishes if and only if the canonical Genuine readout vanishes. -/
theorem finiteC3GenuineTailGreenDefect_eq_zero_iff_genuine_zero
    (M : ℕ) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    finiteC3GenuineTailGreenDefect M s = 0 ↔
      genuineContinuation s = 0 := by
  rw [finiteC3GenuineTailGreenDefect_eq_neg_factor_mul_genuine M hs]
  have hfactor : cpChartFactor 3 s ≠ 0 :=
    cpChartFactor_ne_zero_on_genuineCriticalStrip 3 (by norm_num) hs
  simp [hfactor]

/-- Green-language form of the special kernel property.  At a Genuine zero,
the coupled finite Green flux equals the pure Green form plus the determined
outer-endpoint/tail boundary, at every cutoff. -/
theorem finiteC3TailResolvedGreenIdentity_of_genuine_zero
    (M : ℕ) {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    finiteCanonicalTfvdCoupledGenuineGreenFlux 3 M s =
      greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M) (reflectedParameter s)) +
        finiteC3GenuineTailGreenBoundary M s := by
  have hdefect : finiteC3GenuineTailGreenDefect M s = 0 :=
    (finiteC3GenuineTailGreenDefect_eq_zero_iff_genuine_zero M hs).2 hzero
  exact sub_eq_zero.mp hdefect

/-- Conversely, the tail-resolved Green identity at one cutoff already
recovers the Genuine zero.  No critical-line or isotropy premise occurs. -/
theorem finiteC3TailResolvedGreenIdentity_iff_genuine_zero
    (M : ℕ) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    (finiteCanonicalTfvdCoupledGenuineGreenFlux 3 M s =
      greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M) (reflectedParameter s)) +
        finiteC3GenuineTailGreenBoundary M s) ↔
      genuineContinuation s = 0 := by
  simpa [finiteC3GenuineTailGreenDefect, sub_eq_zero] using
    finiteC3GenuineTailGreenDefect_eq_zero_iff_genuine_zero M hs

/-- The retained endpoint and bracket tail both disappear at infinity.  This
uses only summability of the bracket series, not a zero hypothesis. -/
theorem finiteC3GenuineTailGreenBoundary_tendsto_zero
    {s : ℂ} (hs : -1 < s.re) :
    Tendsto (fun M : ℕ ↦ finiteC3GenuineTailGreenBoundary M s)
      atTop (nhds 0) := by
  have hthree : Tendsto (fun M : ℕ ↦ 3 * M) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with M hM
    omega
  have houter := (finiteReflectedOuterEndpoint_tendsto_zero s).comp hthree
  have htail := realCpBracketCutoffTail_tendsto_zero
    3 (by norm_num) hs
  simpa [finiteC3GenuineTailGreenBoundary, Function.comp_def] using
    houter.add htail

/-- At a Genuine zero, the coupled Green ledger and the pure bracket-resolved
Green form become asymptotically equal because their exact difference is the
vanishing endpoint/tail boundary.  This does not say that either side tends to
zero. -/
theorem finiteC3CoupledGreenFlux_sub_greenForm_tendsto_zero_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun M : ℕ ↦
        finiteCanonicalTfvdCoupledGenuineGreenFlux 3 M s -
          greenForm (𝕜 := ℂ)
            (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
            (finiteC3GenuineBracketGreenBoundaryPair
              (3 * M) (reflectedParameter s)))
      atTop (nhds 0) := by
  have hboundary := finiteC3GenuineTailGreenBoundary_tendsto_zero
    (s := s) (by linarith [hs.1])
  have hfunctions :
      (fun M : ℕ ↦
        finiteCanonicalTfvdCoupledGenuineGreenFlux 3 M s -
          greenForm (𝕜 := ℂ)
            (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
            (finiteC3GenuineBracketGreenBoundaryPair
              (3 * M) (reflectedParameter s))) =
        (fun M : ℕ ↦ finiteC3GenuineTailGreenBoundary M s) := by
    funext M
    rw [finiteC3TailResolvedGreenIdentity_of_genuine_zero M hs hzero]
    ring
  rw [hfunctions]
  exact hboundary

/-- A concise predicate for points whose complete family of finite C3 Green
ledgers obeys the canonical nonlocal tail law. -/
def IsC3TailCoherentGreenKernelPoint (s : ℂ) : Prop :=
  ∀ M : ℕ, finiteC3GenuineTailGreenDefect M s = 0

/-- Capstone: inside the open strip, the Genuine kernel is exactly the locus of
tail-coherent C3 Green kernel points.  The statement preserves the tail and
does not identify this locus with pure Green isotropy. -/
theorem isC3TailCoherentGreenKernelPoint_iff_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    IsC3TailCoherentGreenKernelPoint s ↔
      genuineContinuation s = 0 := by
  constructor
  · intro hcoherent
    exact
      (finiteC3GenuineTailGreenDefect_eq_zero_iff_genuine_zero 0 hs).1
        (hcoherent 0)
  · intro hzero M
    exact
      (finiteC3GenuineTailGreenDefect_eq_zero_iff_genuine_zero M hs).2 hzero

end

end NativeCarryC3Crosswalk
