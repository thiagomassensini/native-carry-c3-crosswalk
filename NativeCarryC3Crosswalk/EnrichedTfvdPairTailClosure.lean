import NativeCarryC3Crosswalk.EnrichedTfvdPairTransport
import NativeCarryC3Crosswalk.GenuineTailGreenTransport
import NativeCarryC3Crosswalk.GenuineBracketGreenFactorization

/-!
# Tail-completed closure audit for the enriched TFVD pair

The enriched value/log-jet transport retains the complete C3 Green diagonal,
while the Genuine tail transport retains the nonlocal part of the same
bracket series.  This module composes those two constructions without
replacing either one by a scalar surrogate.

For the canonical arithmetic pair, define the corrected pair boundary by
subtracting its independently constructed provenance channels.  Its value
readout is completed by the exact unresolved bracket tail.  The resulting
finite identity is

`PairTailDefect = -(valueReadout + bracketTail)`.

Inside the Genuine strip this becomes

`PairTailDefect = -cpChartFactor 3 s * genuineContinuation s`.

Thus the requested nonlocal defect factorization really does close on the
enriched pair, for every parameter and before a zero is assumed.  At a
Genuine zero the tail-resolved pair ledger therefore closes at every cutoff.

The final section separates this statement from pure Green isotropy.  The
corrected pair boundary is literally the reflected Green form, and its
convergence to zero is equivalent to `Re(s) = 1 / 2`.  Consequently the rule
that every Genuine zero closes that pure boundary is exactly the existing
strong-nonvanishing frontier.  No such rule is inserted here.
-/

open scoped Topology

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary
open Filter

noncomputable section

/-- The pair boundary after removing the explicit, provenance-labelled leg
transport.  The subtraction is performed only after both enriched legs and
all three C3 residues have been retained. -/
def finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) : ℂ :=
  finiteC3EnrichedTfvdPairBoundaryForm M
      (finiteC3EnrichedTfvdPairTransport M kappa omega s
        (canonicalEnrichedTfvdValueLogJetPair kappa omega s)) -
    finiteCanonicalTfvdSameSGreenProvenanceDefect 3 M s

/-- The corrected enriched-pair boundary is exactly the bracket-resolved C3
Green form.  No zero, strip, tail, or critical-line hypothesis occurs. -/
theorem finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary_eq_greenForm
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary
        M kappa omega s =
      greenForm (𝕜 := ℂ)
        (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
        (finiteC3GenuineBracketGreenBoundaryPair
          (3 * M) (reflectedParameter s)) := by
  unfold finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary
  rw [finiteC3EnrichedTfvdPairBoundaryForm_canonical]
  exact finiteCanonicalSeededTfvdBoundary_sub_provenance_eq_genuineGreenForm
    M hkappa omega homega s

/-- The nonlocal value coordinate of the same enriched pair: its scalar
Genuine readout plus the unresolved tail of that very bracket series. -/
def finiteC3CanonicalEnrichedTfvdPairTailReadout
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) : ℂ :=
  (finiteC3EnrichedTfvdPairTransport M kappa omega s
      (canonicalEnrichedTfvdValueLogJetPair kappa omega s)).valueReadout +
    realCpBracketCutoffTail 3 M s

/-- Head plus tail recovers the complete infinite bracket chart exactly. -/
theorem finiteC3CanonicalEnrichedTfvdPairTailReadout_eq_chart
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : -1 < s.re) :
    finiteC3CanonicalEnrichedTfvdPairTailReadout M kappa omega s =
      bracketedDirichletChart 3 s := by
  have htransport :=
    finiteC3EnrichedTfvdPairTransport_canonical
      M hkappa omega homega s
  dsimp only at htransport
  unfold finiteC3CanonicalEnrichedTfvdPairTailReadout
  rw [htransport.1]
  exact (bracketedDirichletChart_eq_finite_add_cutoffTail
    3 M (by norm_num) hs).symm

/-- On the open strip, the tail-completed enriched value readout is the
nonvanishing C3 chart factor times the Genuine continuation. -/
theorem finiteC3CanonicalEnrichedTfvdPairTailReadout_eq_factor_mul_genuine
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    finiteC3CanonicalEnrichedTfvdPairTailReadout M kappa omega s =
      cpChartFactor 3 s * genuineContinuation s := by
  rw [finiteC3CanonicalEnrichedTfvdPairTailReadout_eq_chart
      M hkappa omega homega (by linarith [hs.1]),
    bracketedDirichletChart_eq_cpChartFactor_mul_genuineContinuation
      3 (by norm_num) (by norm_num) hs]

/-- Tail-resolved boundary defect written entirely with the enriched pair.
The pure Green coordinate is not substituted by a scalar: it is the corrected
pair boundary retained by `J_M`. -/
def finiteC3EnrichedTfvdPairTailDefect
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) : ℂ :=
  finiteCanonicalTfvdCoupledGenuineGreenFlux 3 M s -
    (finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary
        M kappa omega s +
      finiteC3GenuineTailGreenBoundary M s)

/-- The pair-level defect is literally the previously audited nonlocal Green
defect.  This equality is the typed crosswalk between the two constructions. -/
theorem finiteC3EnrichedTfvdPairTailDefect_eq_genuineTailGreenDefect
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    finiteC3EnrichedTfvdPairTailDefect M kappa omega s =
      finiteC3GenuineTailGreenDefect M s := by
  unfold finiteC3EnrichedTfvdPairTailDefect
    finiteC3GenuineTailGreenDefect
  rw [finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary_eq_greenForm
    M hkappa omega homega s]

/-- Universal nonlocal factorization requested of the enriched transport:
the boundary defect is the negative of the tail-completed Genuine value
readout.  It holds before any zero or critical-line hypothesis. -/
theorem finiteC3EnrichedTfvdPairTailDefect_eq_neg_tailReadout
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    finiteC3EnrichedTfvdPairTailDefect M kappa omega s =
      -finiteC3CanonicalEnrichedTfvdPairTailReadout M kappa omega s := by
  rw [finiteC3EnrichedTfvdPairTailDefect_eq_genuineTailGreenDefect
      M hkappa omega homega s,
    finiteC3GenuineTailGreenDefect_eq_neg_finiteChart_add_tail]
  have htransport :=
    finiteC3EnrichedTfvdPairTransport_canonical
      M hkappa omega homega s
  dsimp only at htransport
  unfold finiteC3CanonicalEnrichedTfvdPairTailReadout
  rw [htransport.1]

/-- In the strip, the universal pair defect factors through the Genuine
readout with the independently nonzero C3 multiplier. -/
theorem finiteC3EnrichedTfvdPairTailDefect_eq_neg_factor_mul_genuine
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    finiteC3EnrichedTfvdPairTailDefect M kappa omega s =
      -(cpChartFactor 3 s * genuineContinuation s) := by
  rw [finiteC3EnrichedTfvdPairTailDefect_eq_neg_tailReadout
      M hkappa omega homega s,
    finiteC3CanonicalEnrichedTfvdPairTailReadout_eq_factor_mul_genuine
      M hkappa omega homega hs]

/-- Exact kernel transport on the enriched pair. -/
theorem finiteC3EnrichedTfvdPairTailDefect_eq_zero_iff_genuine_zero
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    finiteC3EnrichedTfvdPairTailDefect M kappa omega s = 0 ↔
      genuineContinuation s = 0 := by
  rw [finiteC3EnrichedTfvdPairTailDefect_eq_neg_factor_mul_genuine
      M hkappa omega homega hs]
  have hfactor : cpChartFactor 3 s ≠ 0 :=
    cpChartFactor_ne_zero_on_genuineCriticalStrip 3 (by norm_num) hs
  simp [hfactor]

/-- At a Genuine zero, the complete finite tail-resolved identity closes on
the enriched pair.  This is an exact equality at every cutoff, not a limit. -/
theorem finiteC3TailResolvedEnrichedTfvdPairIdentity_of_genuine_zero
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    finiteCanonicalTfvdCoupledGenuineGreenFlux 3 M s =
      finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary
          M kappa omega s +
        finiteC3GenuineTailGreenBoundary M s := by
  have hdefect :
      finiteC3EnrichedTfvdPairTailDefect M kappa omega s = 0 :=
    (finiteC3EnrichedTfvdPairTailDefect_eq_zero_iff_genuine_zero
      M hkappa omega homega hs).2 hzero
  exact sub_eq_zero.mp hdefect

/-- The nonlocal endpoint/tail is the whole asymptotic difference between the
coupled Green ledger and the corrected enriched-pair boundary at a Genuine
zero. -/
theorem finiteC3CoupledGreenFlux_sub_correctedPairBoundary_tendsto_zero_of_genuine_zero
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun M : ℕ ↦
        finiteCanonicalTfvdCoupledGenuineGreenFlux 3 M s -
          finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary
            M kappa omega s)
      atTop (nhds 0) := by
  have hboundary := finiteC3GenuineTailGreenBoundary_tendsto_zero
    (s := s) (by linarith [hs.1])
  have hfunctions :
      (fun M : ℕ ↦
        finiteCanonicalTfvdCoupledGenuineGreenFlux 3 M s -
          finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary
            M kappa omega s) =
        (fun M : ℕ ↦ finiteC3GenuineTailGreenBoundary M s) := by
    funext M
    rw [finiteC3TailResolvedEnrichedTfvdPairIdentity_of_genuine_zero
      M hkappa omega homega hs hzero]
    ring
  rw [hfunctions]
  exact hboundary

/-- At a Genuine zero, the coupled Green ledger has the same explicit limit
as the reflected Green bulk.  The endpoint/tail coordinate disappears, but
the radial bulk is retained. -/
theorem finiteC3CoupledGreenFlux_tendsto_radialBulk_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun M : ℕ ↦ finiteCanonicalTfvdCoupledGenuineGreenFlux 3 M s)
      atTop
      (nhds
        (((cpRadialDifference 3
            (criticalDisplacement s.re) : ℝ) : ℂ) *
          infiniteReflectedGradientPairing s)) := by
  have hgreen :=
    (greenForm_finiteC3GenuineBracketGreenBoundaryPair_tendsto hs).comp
      tendsto_three_mul_atTop
  have hboundary := finiteC3GenuineTailGreenBoundary_tendsto_zero
    (s := s) (by linarith [hs.1])
  have hsum := hgreen.add hboundary
  have hfunctions :
      (fun M : ℕ ↦ finiteCanonicalTfvdCoupledGenuineGreenFlux 3 M s) =
        (fun M : ℕ ↦
          greenForm (𝕜 := ℂ)
              (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
              (finiteC3GenuineBracketGreenBoundaryPair
                (3 * M) (reflectedParameter s)) +
            finiteC3GenuineTailGreenBoundary M s) := by
    funext M
    exact finiteC3TailResolvedGreenIdentity_of_genuine_zero M hs hzero
  rw [hfunctions]
  simpa [Function.comp_def] using hsum

/-- The unscaled angular correction is not an asymptotically vanishing tail
at a Genuine zero.  Its limit is the negative nonzero reflected pairing. -/
theorem finiteCanonicalAngularGreenCorrection_not_tendsto_zero_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    ¬ Tendsto
        (fun M : ℕ ↦ finiteCanonicalAngularGreenCorrection M s)
        atTop (nhds 0) := by
  intro hcloses
  have hlimit :=
    finiteCanonicalAngularGreenCorrection_tendsto_neg_infinitePairing_of_genuine_zero
      hs hzero
  have hneg : -infiniteReflectedGradientPairing s = 0 :=
    tendsto_nhds_unique hlimit hcloses
  exact infiniteReflectedGradientPairing_ne_zero hs (neg_eq_zero.mp hneg)

/-- Pointwise form of the remaining gate: even after assuming a Genuine
zero, the coupled Green ledger closes exactly when the radial displacement is
critical.  Thus zero-to-coupled-Green closure cannot be obtained from the
tail identity alone. -/
theorem finiteC3CoupledGreenFlux_tendsto_zero_iff_re_eq_half_of_genuine_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
        (fun M : ℕ ↦ finiteCanonicalTfvdCoupledGenuineGreenFlux 3 M s)
        atTop (nhds 0) ↔
      s.re = (1 : ℝ) / 2 := by
  constructor
  · intro hcloses
    have hlimit :=
      finiteC3CoupledGreenFlux_tendsto_radialBulk_of_genuine_zero hs hzero
    have hproduct :
        (((cpRadialDifference 3
            (criticalDisplacement s.re) : ℝ) : ℂ) *
          infiniteReflectedGradientPairing s) = 0 :=
      tendsto_nhds_unique hlimit hcloses
    have henergy : infiniteReflectedGradientPairing s ≠ 0 :=
      infiniteReflectedGradientPairing_ne_zero hs
    have hcoefficient :
        ((cpRadialDifference 3
          (criticalDisplacement s.re) : ℝ) : ℂ) = 0 :=
      (mul_eq_zero.mp hproduct).resolve_right henergy
    have hradial :
        cpRadialDifference 3 (criticalDisplacement s.re) = 0 := by
      exact_mod_cast hcoefficient
    have hcritical : criticalDisplacement s.re = 0 :=
      (cpRadialDifference_eq_zero_iff
        3 (by norm_num) (criticalDisplacement s.re)).1 hradial
    unfold criticalDisplacement at hcritical
    linarith
  · intro hre
    have hcritical : criticalDisplacement s.re = 0 := by
      unfold criticalDisplacement
      linarith
    have hlimit :=
      finiteC3CoupledGreenFlux_tendsto_radialBulk_of_genuine_zero hs hzero
    rw [hcritical] at hlimit
    simpa [cpRadialDifference] using hlimit

/-! ## Exact pure-Green frontier -/

/-- Closure of the corrected enriched-pair boundary, kept separate from
closure of its tail-resolved defect. -/
def C3EnrichedTfvdCorrectedPairBoundaryClosesAt
    (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) : Prop :=
  Tendsto
    (fun M : ℕ ↦
      finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary
        M kappa omega s)
    atTop (nhds 0)

/-- The pure corrected pair boundary closes exactly at quadratic equilibrium.
This has no Genuine-zero hypothesis. -/
theorem c3EnrichedTfvdCorrectedPairBoundaryClosesAt_iff_re_eq_half
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    C3EnrichedTfvdCorrectedPairBoundaryClosesAt kappa omega s ↔
      s.re = (1 : ℝ) / 2 := by
  constructor
  · intro hclosure
    have hthree : Tendsto (fun M : ℕ ↦ 3 * M) atTop atTop := by
      apply tendsto_atTop.2
      intro N
      filter_upwards [eventually_ge_atTop N] with M hM
      omega
    have hlimit :=
      (greenForm_finiteC3GenuineBracketGreenBoundaryPair_tendsto hs).comp
        hthree
    have hfunctions :
        (fun M : ℕ ↦
          finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary
            M kappa omega s) =
          (fun M : ℕ ↦
            greenForm (𝕜 := ℂ)
              (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
              (finiteC3GenuineBracketGreenBoundaryPair
                (3 * M) (reflectedParameter s))) := by
      funext M
      exact
        finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary_eq_greenForm
          M hkappa omega homega s
    unfold C3EnrichedTfvdCorrectedPairBoundaryClosesAt at hclosure
    rw [hfunctions] at hclosure
    have hlimit' :
        Tendsto
          (fun M : ℕ ↦
            greenForm (𝕜 := ℂ)
              (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
              (finiteC3GenuineBracketGreenBoundaryPair
                (3 * M) (reflectedParameter s)))
          atTop
          (nhds
            (((cpRadialDifference 3
                (criticalDisplacement s.re) : ℝ) : ℂ) *
              infiniteReflectedGradientPairing s)) := by
      simpa [Function.comp_def] using hlimit
    have hproduct :
        (((cpRadialDifference 3
            (criticalDisplacement s.re) : ℝ) : ℂ) *
          infiniteReflectedGradientPairing s) = 0 :=
      tendsto_nhds_unique hlimit' hclosure
    have henergy : infiniteReflectedGradientPairing s ≠ 0 :=
      infiniteReflectedGradientPairing_ne_zero hs
    have hcoefficient :
        ((cpRadialDifference 3
          (criticalDisplacement s.re) : ℝ) : ℂ) = 0 :=
      (mul_eq_zero.mp hproduct).resolve_right henergy
    have hradial :
        cpRadialDifference 3 (criticalDisplacement s.re) = 0 := by
      exact_mod_cast hcoefficient
    have hcritical : criticalDisplacement s.re = 0 :=
      (cpRadialDifference_eq_zero_iff
        3 (by norm_num) (criticalDisplacement s.re)).1 hradial
    unfold criticalDisplacement at hcritical
    linarith
  · intro hre
    have hcritical : criticalDisplacement s.re = 0 := by
      unfold criticalDisplacement
      linarith
    have hfunctions :
        (fun M : ℕ ↦
          finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary
            M kappa omega s) =
          (fun _ : ℕ ↦ (0 : ℂ)) := by
      funext M
      rw [finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary_eq_greenForm
          M hkappa omega homega s,
        greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_radialFactorization,
        hcritical]
      simp [cpRadialDifference]
    unfold C3EnrichedTfvdCorrectedPairBoundaryClosesAt
    rw [hfunctions]
    exact tendsto_const_nhds

/-- Uniform activation statement whose logical strength is audited below. -/
def GenuineZerosCloseC3EnrichedTfvdCorrectedPairBoundary
    (kappa : ℂ) (omega : ℕ → ℂ) : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    genuineContinuation s = 0 →
      C3EnrichedTfvdCorrectedPairBoundaryClosesAt kappa omega s

/-- Keeping the full pair removes the finite provenance obstruction, but it
does not turn scalar Genuine cancellation into pure Green closure.  That
activation is exactly the strong nonvanishing statement. -/
theorem genuineZerosCloseC3EnrichedTfvdCorrectedPairBoundary_iff_strongNonvanishing
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) :
    GenuineZerosCloseC3EnrichedTfvdCorrectedPairBoundary kappa omega ↔
      GenuineStrongNonvanishingInStrip := by
  constructor
  · intro hcloses s hs hoff hzero
    have hre :=
      (c3EnrichedTfvdCorrectedPairBoundaryClosesAt_iff_re_eq_half
        hkappa omega homega hs).1 (hcloses hs hzero)
    exact hoff hre
  · intro hstrong s hs hzero
    apply
      (c3EnrichedTfvdCorrectedPairBoundaryClosesAt_iff_re_eq_half
        hkappa omega homega hs).2
    by_contra hoff
    exact (hstrong hs hoff) hzero

end

end NativeCarryC3Crosswalk
