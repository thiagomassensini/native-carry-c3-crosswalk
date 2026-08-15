import NativeCarryC3Crosswalk.StructuralTfvdGreenDefect
import NativeCarryC3Crosswalk.EnrichedTfvdPairTransport
import GreenFrame.Concrete.Analysis.StaticPoisson

/-!
# Full endpoint, Poisson return, and structural defect

This module separates the complete endpoint from its scalar readouts.

For the normalized Green-frame split, exact Poisson reconstruction shows that
zero full endpoint implies zero bulk.  If a realization identifies that bulk
energy with the structural carry--Green defect, the existing rigidity theorem
then gives the half-abscissa.

For the finite enriched C3 construction, the full direct/reflected Green port
already factors the Green bulk exactly.  The canonical full Green port is
nonzero at every nonempty cutoff in the open strip.  At a Genuine zero the
tail-completed scalar readout vanishes while this complete port remains
nonzero.  No scalar readout is identified with the full endpoint.
-/

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary

noncomputable section

/-! ## Exact Poisson consequence for a complete endpoint -/

/-- Exact Poisson reconstruction sends a zero normalized full endpoint to
zero normalized bulk. -/
theorem normalizedFullEndpoint_zero_implies_bulk_zero
    {H E B : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
    {T : H →L[ℂ] GreenFrame.Concrete.HilbertSum E B}
    (bounds : GreenFrame.Concrete.SplitComplexFrameBounds T) (x : H)
    (hendpoint : GreenFrame.Concrete.normalizedExternal T x = 0) :
    GreenFrame.Concrete.normalizedBulk T x = 0 := by
  have hrange :
      (GreenFrame.Concrete.normalizedExternal T).rangeRestrict x = 0 := by
    apply Subtype.ext
    exact hendpoint
  rw [← GreenFrame.Concrete.restrictedPoisson_apply_external bounds x,
    hrange, map_zero]

/-- If the normalized bulk energy realizes the structural carry--Green
defect, a zero full endpoint forces that defect to vanish. -/
theorem structuralDefect_zero_of_normalizedFullEndpoint_zero
    {H E B : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
    {T : H →L[ℂ] GreenFrame.Concrete.HilbertSum E B}
    (bounds : GreenFrame.Concrete.SplitComplexFrameBounds T) (x : H)
    (p : ℕ) (s : ℂ)
    (hendpoint : GreenFrame.Concrete.normalizedExternal T x = 0)
    (hbulkEnergy : structuralCarryGreenDefectEnergy p s =
      ‖GreenFrame.Concrete.normalizedBulk T x‖ ^ 2) :
    structuralCarryGreenDefectEnergy p s = 0 := by
  have hbulk := normalizedFullEndpoint_zero_implies_bulk_zero
    bounds x hendpoint
  rw [hbulk, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hbulkEnergy
  exact hbulkEnergy

/-- Coordinate consequence of the full-endpoint Poisson mechanism. -/
theorem re_eq_half_of_normalizedFullEndpoint_zero
    {H E B : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
    {T : H →L[ℂ] GreenFrame.Concrete.HilbertSum E B}
    (bounds : GreenFrame.Concrete.SplitComplexFrameBounds T) (x : H)
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hendpoint : GreenFrame.Concrete.normalizedExternal T x = 0)
    (hbulkEnergy : structuralCarryGreenDefectEnergy p s =
      ‖GreenFrame.Concrete.normalizedBulk T x‖ ^ 2) :
    s.re = (1 : ℝ) / 2 := by
  apply (structuralCarryGreenDefectEnergy_eq_zero_iff_re_eq_half
    p hp hs).1
  exact structuralDefect_zero_of_normalizedFullEndpoint_zero
    bounds x p s hendpoint hbulkEnergy

/-! ## Complete finite C3 endpoint -/

/-- Direct and reflected provenance-preserving C3 Green endpoints, before
scalar synthesis. -/
abbrev C3FullReflectedStatePort (M : ℕ) :=
  FiniteC3GreenPortCarrier M × FiniteC3GreenPortCarrier M

/-- Canonical direct/reflected full C3 port. -/
def canonicalC3FullReflectedStatePort (M : ℕ) (s : ℂ) :
    C3FullReflectedStatePort M :=
  (finiteC3GenuineBracketGreenBoundaryPair M s,
    finiteC3GenuineBracketGreenBoundaryPair M (reflectedParameter s))

/-- Green bulk read directly from the complete direct/reflected state port. -/
def c3FullStatePortGreenBulk {M : ℕ}
    (endpoint : C3FullReflectedStatePort M) : ℂ :=
  greenForm endpoint.1 endpoint.2

/-- The full-port Green bulk has the exact radial factorization already
proved for the bracket-resolved C3 endpoints. -/
theorem c3FullStatePortGreenBulk_canonical
    (M : ℕ) (s : ℂ) :
    c3FullStatePortGreenBulk
        (canonicalC3FullReflectedStatePort M s) =
      ((cpRadialDifference 3
        (criticalDisplacement s.re) : ℝ) : ℂ) *
        finiteReflectedGradientPairing M s := by
  exact
    greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_radialFactorization
      M s

/-- A zero full endpoint has zero Green bulk. -/
theorem c3FullStatePortGreenBulk_eq_zero_of_fullEndpoint_zero
    {M : ℕ} {endpoint : C3FullReflectedStatePort M}
    (hendpoint : endpoint = 0) :
    c3FullStatePortGreenBulk endpoint = 0 := by
  rw [hendpoint]
  simp [c3FullStatePortGreenBulk]

/-- At a nonempty cutoff, zero canonical full-port Green bulk forces the
structural carry--Green defect energy to vanish. -/
theorem structuralDefect_zero_of_canonicalFullStateGreenBulk_zero
    (M : ℕ) (hM : 0 < M)
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hbulk : c3FullStatePortGreenBulk
      (canonicalC3FullReflectedStatePort M s) = 0) :
    structuralCarryGreenDefectEnergy p s = 0 := by
  have hfactor := c3FullStatePortGreenBulk_canonical M s
  rw [hbulk] at hfactor
  have hpair : finiteReflectedGradientPairing M s ≠ 0 :=
    finiteReflectedGradientPairing_ne_zero hM hs
  have hradialComplex :
      ((cpRadialDifference 3
        (criticalDisplacement s.re) : ℝ) : ℂ) = 0 := by
    exact (mul_eq_zero.mp hfactor.symm).resolve_right hpair
  have hradial :
      cpRadialDifference 3 (criticalDisplacement s.re) = 0 := by
    exact_mod_cast hradialComplex
  have hcritical : criticalDisplacement s.re = 0 :=
    (cpRadialDifference_eq_zero_iff
      3 (by norm_num) (criticalDisplacement s.re)).1 hradial
  have hre : s.re = (1 : ℝ) / 2 := by
    unfold criticalDisplacement at hcritical
    linarith
  exact (structuralCarryGreenDefectEnergy_eq_zero_iff_re_eq_half
    p hp hs).2 hre

/-- Full C3 endpoint closure implies, in order, zero Green bulk, zero
structural defect energy, and the half-abscissa. -/
theorem fullC3Endpoint_zero_structuralDefect_zero_re_eq_half
    (M : ℕ) (hM : 0 < M)
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hendpoint : canonicalC3FullReflectedStatePort M s = 0) :
    c3FullStatePortGreenBulk
        (canonicalC3FullReflectedStatePort M s) = 0 ∧
      structuralCarryGreenDefectEnergy p s = 0 ∧
      s.re = (1 : ℝ) / 2 := by
  have hbulk := c3FullStatePortGreenBulk_eq_zero_of_fullEndpoint_zero
    hendpoint
  have hdefect :=
    structuralDefect_zero_of_canonicalFullStateGreenBulk_zero
      M hM p hp hs hbulk
  exact ⟨hbulk, hdefect,
    (structuralCarryGreenDefectEnergy_eq_zero_iff_re_eq_half
      p hp hs).1 hdefect⟩

/-! ## Canonical full port and Genuine scalar readout -/

/-- The canonical full Green endpoint is nonzero at every nonempty cutoff in
the open strip. -/
theorem finiteC3GenuineFullGreenEndpoint_ne_zero
    (M : ℕ) (hM : 0 < M)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    finiteC3GenuineBracketGreenBoundaryPair M s ≠ 0 := by
  intro hzero
  have hsnd :
      (finiteC3GenuineBracketGreenBoundaryPair M s).2 = 0 :=
    congrArg Prod.snd hzero
  have hpairZero : finiteReflectedGradientPairing M s = 0 := by
    unfold finiteReflectedGradientPairing
    apply Finset.sum_eq_zero
    intro n hn
    have hnlt : n < M := Finset.mem_range.mp hn
    have hcoordinate := congrArg
      (fun v : FiniteC3GreenBoundarySpace M => v ⟨n, hnlt⟩) hsnd
    simp only [finiteC3GenuineBracketGreenBoundaryPair_snd_apply,
      PiLp.zero_apply] at hcoordinate
    rw [hcoordinate]
    simp
  exact (finiteReflectedGradientPairing_ne_zero hM hs) hpairZero

/-- The full Green port returned by the canonical enriched TFVD transport is
nonzero at a nonempty cutoff in the open strip. -/
theorem canonicalEnrichedTfvdFullStatePort_ne_zero
    (M : ℕ) (hM : 0 < M)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    (finiteC3EnrichedTfvdPairTransport M kappa omega s
      (canonicalEnrichedTfvdValueLogJetPair kappa omega s)).greenPort ≠ 0 := by
  change finiteC3EnrichedTfvdValueGreenPort M kappa omega s
      (canonicalSeededEnrichedTfvdGenuinePort kappa omega s) ≠ 0
  rw [finiteC3EnrichedTfvdValueGreenPort_canonical
    M hkappa omega homega s]
  exact finiteC3GenuineFullGreenEndpoint_ne_zero
    (M * 3) (Nat.mul_pos hM (by norm_num)) hs

/-- At a Genuine zero, the tail-completed scalar readout vanishes while the
canonical full enriched Green port remains nonzero. -/
theorem genuineZero_tailStateReadout_zero_fullStatePort_ne_zero
    (M : ℕ) (hM : 0 < M)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    finiteC3CanonicalEnrichedTfvdPairTailReadout
        M kappa omega s = 0 ∧
      (finiteC3EnrichedTfvdPairTransport M kappa omega s
        (canonicalEnrichedTfvdValueLogJetPair kappa omega s)).greenPort ≠ 0 := by
  constructor
  · rw [finiteC3CanonicalEnrichedTfvdPairTailReadout_eq_factor_mul_genuine
      M hkappa omega homega hs, hzero, mul_zero]
  · exact canonicalEnrichedTfvdFullStatePort_ne_zero
      M hM hkappa omega homega hs

end

end NativeCarryC3Crosswalk
