import NativeCarryC3Crosswalk.EnrichedBoundaryCarrier
import CPFormal.Analytic.CpFiniteSeededTfvdGreenIdentity

/-!
# Genuine bracket to Green: an unconditional finite identity

This module records the direct route remembered in the research chronology:

`Genuine bracket -> resolved gradient -> enriched TFVD port -> Green form`.

No zero predicate, limiting argument, critical-line hypothesis, or selected
inverse occurs.  The first Green coordinate is built from the differentiated
Genuine bracket residual itself.  The existing universal bracket identity
then identifies that coordinate with the C3 block gradient, and the abstract
boundary `greenForm` becomes literally the finite oriented Genuine Green
flux and the preserved TFVD diagonal.

The seeded form gives the corresponding finite ledger.  After subtracting
the independently defined provenance channels, its boundary form is exactly
the same abstract Green form.  Separately, the scalar readout of the same
seeded TFVD data is the finite bracketed Genuine chart.  These are identities
of the finite constructions for every complex parameter; zeros enter only
in later applications, not here.
-/

open scoped BigOperators ComplexConjugate

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary

noncomputable section

/-- C3 boundary pair whose first coordinate is constructed directly from
the differentiated and canonically normalized Genuine bracket residual. -/
def finiteC3GenuineBracketGreenBoundaryPair (M : ℕ) (s : ℂ) :
    FiniteC3GreenPortCarrier M :=
  (WithLp.toLp 2 (fun n : Fin M ↦
      phaseNormalizedCpGenuineGreenGradient 3 s n),
    WithLp.toLp 2 (fun n : Fin M ↦
      positiveDirichletGradient s n))

@[simp] theorem finiteC3GenuineBracketGreenBoundaryPair_fst_apply
    (M : ℕ) (s : ℂ) (n : Fin M) :
    (finiteC3GenuineBracketGreenBoundaryPair M s).1 n =
      phaseNormalizedCpGenuineGreenGradient 3 s n :=
  rfl

@[simp] theorem finiteC3GenuineBracketGreenBoundaryPair_snd_apply
    (M : ℕ) (s : ℂ) (n : Fin M) :
    (finiteC3GenuineBracketGreenBoundaryPair M s).2 n =
      positiveDirichletGradient s n :=
  rfl

/-- The bracket source is visible in the boundary coordinate: it is the
phase-normalized difference between the center-block gradient and the
Genuine bracket gradient, divided by the nonzero block size `3`. -/
theorem finiteC3GenuineBracketGreenBoundaryPair_fst_apply_eq_bracketResidual
    (M : ℕ) (s : ℂ) (n : Fin M) :
    (finiteC3GenuineBracketGreenBoundaryPair M s).1 n =
      (3 : ℂ)⁻¹ * cpPhaseNormalizer 3 s *
        (cpCenterBlockGradient 3 (dirichletTerm s) n -
          cpGenuineBracketGradient 3 (dirichletTerm s) n) := by
  rw [finiteC3GenuineBracketGreenBoundaryPair_fst_apply]
  unfold phaseNormalizedCpGenuineGreenGradient cpGenuineGreenGradient
    cpGenuineResolvedGradient
  ring

/-- The boundary pair produced from the Genuine bracket is literally the C3
Green pair.  This is the differentiated bracket identity, not a zero-set
comparison. -/
theorem finiteC3GenuineBracketGreenBoundaryPair_eq_greenBoundaryPair
    (M : ℕ) (s : ℂ) :
    finiteC3GenuineBracketGreenBoundaryPair M s =
      finiteC3GreenBoundaryPair M s := by
  apply Prod.ext
  · ext n
    exact
      phaseNormalizedCpGenuineGreenGradient_eq_phaseNormalizedCpBlockGradient
        3 (by norm_num) s n
  · rfl

/-- Direct Genuine--Green identity.  The abstract boundary form of the
bracket-resolved pair is exactly the oriented flux defined from the Genuine
gradient, at every finite cutoff and every complex parameter. -/
theorem greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_genuineFlux
    (M : ℕ) (s : ℂ) :
    greenForm
        (finiteC3GenuineBracketGreenBoundaryPair M s)
        (finiteC3GenuineBracketGreenBoundaryPair M (reflectedParameter s)) =
      finiteOrientedGenuineCpGreenFlux 3 M s := by
  rw [finiteC3GenuineBracketGreenBoundaryPair_eq_greenBoundaryPair,
    finiteC3GenuineBracketGreenBoundaryPair_eq_greenBoundaryPair,
    greenForm_finiteC3GreenBoundaryPair_eq_orientedFlux,
    finiteOrientedGenuineCpGreenFlux_eq_finiteOrientedCpGreenFlux
      3 M (by norm_num)]

/-- The same unconditional form is exactly the TFVD diagonal.  Thus the
Genuine-first and TFVD-first descriptions are two readings of one finite
Green computation. -/
theorem greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_tfvdDiagonal
    (M : ℕ) (s : ℂ) :
    greenForm
        (finiteC3GenuineBracketGreenBoundaryPair M s)
        (finiteC3GenuineBracketGreenBoundaryPair M (reflectedParameter s)) =
      finiteTfvdCpGreenDiagonal 3 M s := by
  rw [greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_genuineFlux,
    finiteOrientedGenuineCpGreenFlux_eq_tfvdDiagonal
      3 M (by norm_num)]

/-- The seeded TFVD boundary form, after removing its explicitly constructed
local provenance channels, is the abstract Green form of the Genuine bracket
pair.  No term is defined as the residual of this equality. -/
theorem finiteCanonicalSeededTfvdBoundary_sub_provenance_eq_genuineGreenForm
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    finiteCanonicalSeededTfvdSameSBoundaryForm M kappa omega s -
        finiteCanonicalTfvdSameSGreenProvenanceDefect 3 M s =
      greenForm
        (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
        (finiteC3GenuineBracketGreenBoundaryPair
          (3 * M) (reflectedParameter s)) := by
  rw [finiteCanonicalSeededTfvdSameSBoundaryForm_eq_green_add_provenance
      3 (by norm_num) M hkappa omega homega s,
    greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_genuineFlux]
  ring

/-- Direct finite bracket ledger relating the bracketed Genuine chart and the
Green form.  The coupled Genuine Green flux equals the bracket-resolved Green
form plus the moving outer endpoint minus the finite Genuine chart. -/
theorem finiteC3BracketCoupledGenuineGreenFlux_eq_greenForm_add_outer_sub_chart
    (M : ℕ) (s : ℂ) :
    finiteCanonicalTfvdCoupledGenuineGreenFlux 3 M s =
      greenForm
          (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
          (finiteC3GenuineBracketGreenBoundaryPair
            (3 * M) (reflectedParameter s)) +
        finiteReflectedOuterEndpoint (3 * M) s -
          finiteBracketedDirichletChart 3 M s := by
  unfold finiteCanonicalTfvdCoupledGenuineGreenFlux
  rw [finiteCanonicalAngularBracketCoupledBoundary_eq_outer_sub_finiteChart,
    greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_genuineFlux]
  ring

/-- One theorem exposing both readouts of the same canonical seeded TFVD
data: its scalar readout is the finite Genuine chart, while its corrected
boundary-form readout is the Green form of the bracket-resolved pair. -/
theorem finiteC3GenuineBracketTfvdGreen_capstone
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    (finiteSeededEnrichedTfvdGenuineReadout M kappa omega
        (canonicalSeededEnrichedTfvdGenuinePort kappa omega s) =
      finiteBracketedDirichletChart 3 M s) ∧
    (finiteCanonicalSeededTfvdSameSBoundaryForm M kappa omega s -
        finiteCanonicalTfvdSameSGreenProvenanceDefect 3 M s =
      greenForm
        (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
        (finiteC3GenuineBracketGreenBoundaryPair
          (3 * M) (reflectedParameter s))) := by
  exact
    ⟨finiteSeededEnrichedTfvdGenuineReadout_canonical
        M hkappa omega homega s,
      finiteCanonicalSeededTfvdBoundary_sub_provenance_eq_genuineGreenForm
        M hkappa omega homega s⟩

end

end NativeCarryC3Crosswalk
