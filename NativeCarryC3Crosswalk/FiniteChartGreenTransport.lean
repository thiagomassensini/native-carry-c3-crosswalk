import NativeCarryC3Crosswalk.GenuineTailGreenTransport
import NativeCarryC3Crosswalk.GenuineBracketGreenFactorization
import CPFormal.Analytic.CpGenuineRealAxisPositivity

/-!
# Finite-chart versus reflected-Green transport

This module audits the proposed finite identity

`finite chart = reflected Green form + reflected outer endpoint`

with the already fixed C3 indices and orientations.  It separates two
statements that have the same informal shape but different mathematical
types:

* the finite chart is exactly the **linear angular TFVD trace** plus its
  linear outer value;
* replacing that trace by the **bilinear reflected Green form** is equivalent
  to annihilating the independently defined bracket-coupled Green flux.

The second replacement is therefore not a bookkeeping rearrangement.  A
kernel-checked witness on the real critical point shows that it cannot hold
at every cutoff as a universal identity.  No zero or confinement hypothesis
is used to obtain the exact finite balance.
-/

open scoped Topology

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary
open Filter

noncomputable section

/-- The genuinely linear transport having the requested shape: the finite C3
chart is the angular TFVD trace plus the unpaired outer value at the same
physical endpoint `3 * M`. -/
theorem finiteC3Chart_eq_angularTrace_add_linearOuter
    (M : ℕ) (s : ℂ) :
    finiteBracketedDirichletChart 3 M s =
      finiteCanonicalAngularTrace M s +
        positiveDirichletValue s (3 * M) :=
  finiteBracketedDirichletChart_three_eq_angularTrace_add_outer M s

/-- Exact sign-free rearrangement of the existing finite Green ledger.  All
terms use `M` C3 blocks, `3 * M` Green edges, and the endpoint `3 * M`.
The bracket-coupled Green flux is an independent term and cannot be silently
dropped. -/
theorem finiteC3Chart_add_coupledGreen_eq_greenForm_add_outer
    (M : ℕ) (s : ℂ) :
    finiteBracketedDirichletChart 3 M s +
        finiteCanonicalTfvdCoupledGenuineGreenFlux 3 M s =
      greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M) (reflectedParameter s)) +
        finiteReflectedOuterEndpoint (3 * M) s := by
  rw [finiteC3BracketCoupledGenuineGreenFlux_eq_greenForm_add_outer_sub_chart]
  ring

/-- The proposed replacement of the finite chart by `Green form + outer` is
pointwise equivalent to vanishing of the complete bracket-coupled Green flux.
It is therefore exactly the closure statement, rather than an identity that
precedes closure. -/
theorem finiteC3Chart_eq_greenForm_add_outer_iff_coupledGreen_eq_zero
    (M : ℕ) (s : ℂ) :
    (finiteBracketedDirichletChart 3 M s =
      greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M) (reflectedParameter s)) +
        finiteReflectedOuterEndpoint (3 * M) s) ↔
      finiteCanonicalTfvdCoupledGenuineGreenFlux 3 M s = 0 := by
  rw [finiteC3BracketCoupledGenuineGreenFlux_eq_greenForm_add_outer_sub_chart]
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    linear_combination -h

/-- Exact completed balance after retaining the canonical nonlocal tail.  The
tail occurs once on each side and the independently defined coupled Green
flux remains visible. -/
theorem finiteC3TailCompletedChart_add_coupledGreen_eq_greenForm_add_boundary
    (M : ℕ) (s : ℂ) :
    (finiteBracketedDirichletChart 3 M s +
          realCpBracketCutoffTail 3 M s) +
        finiteCanonicalTfvdCoupledGenuineGreenFlux 3 M s =
      greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M) (reflectedParameter s)) +
        finiteC3GenuineTailGreenBoundary M s := by
  unfold finiteC3GenuineTailGreenBoundary
  rw [finiteC3BracketCoupledGenuineGreenFlux_eq_greenForm_add_outer_sub_chart]
  ring

/-- Adding the same canonical tail does not make the proposed
`completed chart = completed Green` equality automatic: it is still exactly
equivalent to vanishing of the bracket-coupled Green flux. -/
theorem finiteC3TailCompletedChart_eq_greenForm_add_boundary_iff_coupledGreen_eq_zero
    (M : ℕ) (s : ℂ) :
    (finiteBracketedDirichletChart 3 M s +
        realCpBracketCutoffTail 3 M s =
      greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M) (reflectedParameter s)) +
        finiteC3GenuineTailGreenBoundary M s) ↔
      finiteCanonicalTfvdCoupledGenuineGreenFlux 3 M s = 0 := by
  constructor
  · intro hcompleted
    apply
      (finiteC3Chart_eq_greenForm_add_outer_iff_coupledGreen_eq_zero M s).1
    unfold finiteC3GenuineTailGreenBoundary at hcompleted
    linear_combination hcompleted
  · intro hcoupled
    have hfinite :=
      (finiteC3Chart_eq_greenForm_add_outer_iff_coupledGreen_eq_zero M s).2
        hcoupled
    unfold finiteC3GenuineTailGreenBoundary
    linear_combination hfinite

/-- At the real critical point, the proposed bilinear identity cannot hold at
every cutoff.  If it did, the reflected Green form would be identically zero,
the outer endpoint would tend to zero, and uniqueness of limits would force
the infinite C3 chart (hence Genuine) to vanish.  Real-axis positivity proves
that Genuine is nonzero at `1 / 2`.

This is an obstruction inside the open Genuine strip, not merely at a
boundary parameter. -/
theorem exists_cutoff_finiteC3Chart_ne_greenForm_add_outer_at_realHalf :
    ∃ M : ℕ,
      finiteBracketedDirichletChart 3 M (criticalLineParameter 0) ≠
        greenForm (𝕜 := ℂ)
            (finiteC3GenuineBracketGreenBoundaryPair
              (3 * M) (criticalLineParameter 0))
            (finiteC3GenuineBracketGreenBoundaryPair
              (3 * M)
              (reflectedParameter (criticalLineParameter 0))) +
          finiteReflectedOuterEndpoint
            (3 * M) (criticalLineParameter 0) := by
  by_contra hall
  push Not at hall
  let s : ℂ := criticalLineParameter 0
  have hs : s ∈ genuineCriticalStrip := by
    dsimp [s]
    exact criticalLineParameter_mem_genuineCriticalStrip 0
  have hthree : Tendsto (fun M : ℕ ↦ 3 * M) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with M hM
    omega
  have hgreen :
      Tendsto
        (fun M : ℕ ↦
          greenForm (𝕜 := ℂ)
            (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
            (finiteC3GenuineBracketGreenBoundaryPair
              (3 * M) (reflectedParameter s)))
        atTop (nhds 0) := by
    have hbase :=
      (greenForm_finiteC3GenuineBracketGreenBoundaryPair_tendsto_zero_iff
        hs).2 (criticalLineParameter_re 0)
    exact hbase.comp hthree
  have houter :
      Tendsto
        (fun M : ℕ ↦ finiteReflectedOuterEndpoint (3 * M) s)
        atTop (nhds 0) :=
    (finiteReflectedOuterEndpoint_tendsto_zero s).comp hthree
  have hrhs :
      Tendsto
        (fun M : ℕ ↦
          greenForm (𝕜 := ℂ)
              (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
              (finiteC3GenuineBracketGreenBoundaryPair
                (3 * M) (reflectedParameter s)) +
            finiteReflectedOuterEndpoint (3 * M) s)
        atTop (nhds 0) := by
    simpa using hgreen.add houter
  have hfunctions :
      (fun M : ℕ ↦ finiteBracketedDirichletChart 3 M s) =
        (fun M : ℕ ↦
          greenForm (𝕜 := ℂ)
              (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
              (finiteC3GenuineBracketGreenBoundaryPair
                (3 * M) (reflectedParameter s)) +
            finiteReflectedOuterEndpoint (3 * M) s) := by
    funext M
    exact hall M
  have hchartZero :
      Tendsto (fun M : ℕ ↦ finiteBracketedDirichletChart 3 M s)
        atTop (nhds 0) := by
    rw [hfunctions]
    exact hrhs
  have hchartLimit := finiteBracketedDirichletChart_tendsto
    3 (by norm_num) (s := s) (by dsimp [s]; norm_num)
  have hchart : bracketedDirichletChart 3 s = 0 :=
    tendsto_nhds_unique hchartLimit hchartZero
  have hgenuine : genuineContinuation s = 0 :=
    (bracketedDirichletChart_zero_iff_genuineContinuation_zero
      3 (by norm_num) (by norm_num) hs).1 hchart
  have hnonzero : genuineContinuation s ≠ 0 := by
    dsimp [s, criticalLineParameter]
    simpa using
      (genuineContinuation_ofReal_ne_zero
        (show (0 : ℝ) < 1 / 2 by norm_num)
        (show (1 / 2 : ℝ) < 1 by norm_num))
  exact hnonzero hgenuine

end

end NativeCarryC3Crosswalk
