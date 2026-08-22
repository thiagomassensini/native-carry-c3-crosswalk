import NativeCarryC3Crosswalk.CompletedTfvdNaimarkFeasibility
import NativeCarryC3Crosswalk.GenuineBracketGreenIdentity

/-!
# Completed TFVD ledger to the provenance-preserving C3 Green form

The completed same-edge source keeps the ordinary gradient state, its
logarithmic jet, and the later rank-one residual.  The Green boundary form is
already determined before that residual collapse: on one complete C3 block,
the ordinary and log-jet provenance cores recover the two adjacent same-edge
wedges exactly.

This module records that source-level identification and then applies the
existing finite TFVD--Green theorem.  No scalar residual is inverted, no
Wronskian is identified with a raw Gram by definition, and no zero or
critical-line hypothesis is used.
-/

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary

noncomputable section

/-- The two adjacent same-parameter boundary cells read directly from the
ordinary and log-jet provenance legs of one completed TFVD ledger. -/
def completedTfvdGreenLedgerSameSBoundaryCells
    (ledger : CompletedTfvdGreenLedger) : TfvdSameSBoundaryCells :=
  {
    visibleCell := sameSEdgeBoundaryWedge
      (ledger.1.1.2 0) (ledger.1.1.2 1)
      (ledger.1.2.2 0) (ledger.1.2.2 1)
    dormantCell := sameSEdgeBoundaryWedge
      (ledger.1.1.2 1) (ledger.1.1.2 2)
      (ledger.1.2.2 1) (ledger.1.2.2 2)
  }

/-- At cutoff one, the uncollapsed completed ledger recovers literally the
canonical enriched same-parameter TFVD boundary cells of the complete C3
block. -/
theorem completedTfvdGreenLedgerSameSBoundaryCells_seeded
    (s : ℂ) :
    completedTfvdGreenLedgerSameSBoundaryCells
        (seededCompletedTfvdGreenLedger 1 s) =
      canonicalEnrichedTfvdSameSBoundaryCells
        tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) 0 s := by
  rw [canonicalEnrichedTfvdSameSBoundaryCells_eq_gradients
    (kappa := tfvdHaarScale) tfvdHaarScale_ne_zero
    (fun _ : ℕ => (1 : ℂ)) 0 (by norm_num) s]
  apply TfvdSameSBoundaryCells.ext
  · simp [completedTfvdGreenLedgerSameSBoundaryCells,
      c2DirichletGradientPrefixCore_apply,
      c2LogJetPrefixCore_apply]
  · simp [completedTfvdGreenLedgerSameSBoundaryCells,
      c2DirichletGradientPrefixCore_apply,
      c2LogJetPrefixCore_apply]

/-- Total same-parameter boundary of one completed TFVD ledger, formed only
after the visible and dormant cells have both been retained. -/
def completedTfvdGreenLedgerSameSBoundary
    (ledger : CompletedTfvdGreenLedger) : ℂ :=
  (completedTfvdGreenLedgerSameSBoundaryCells ledger).total

/-- The total boundary read from the seeded completed ledger is exactly the
existing canonical seeded TFVD boundary form at one complete C3 block. -/
theorem completedTfvdGreenLedgerSameSBoundary_seeded
    (s : ℂ) :
    completedTfvdGreenLedgerSameSBoundary
        (seededCompletedTfvdGreenLedger 1 s) =
      finiteCanonicalSeededTfvdSameSBoundaryForm
        1 tfvdHaarScale (fun _ : ℕ => (1 : ℂ)) s := by
  rw [completedTfvdGreenLedgerSameSBoundary,
    completedTfvdGreenLedgerSameSBoundaryCells_seeded]
  unfold finiteCanonicalSeededTfvdSameSBoundaryForm
    finiteCanonicalEnrichedTfvdSameSBoundaryTrace
  simp

/-- Subtracting the independently constructed provenance channels from the
boundary read directly from the full completed ledger gives exactly the
provenance-preserving reflected C3 Green form.  This is the sought source to
Green arrow before scalarization. -/
theorem completedTfvdGreenLedgerSameSBoundary_sub_provenance_eq_greenForm
    (s : ℂ) :
    completedTfvdGreenLedgerSameSBoundary
          (seededCompletedTfvdGreenLedger 1 s) -
        finiteCanonicalTfvdSameSGreenProvenanceDefect 3 1 s =
      greenForm
        (finiteC3GenuineBracketGreenBoundaryPair 3 s)
        (finiteC3GenuineBracketGreenBoundaryPair
          3 (reflectedParameter s)) := by
  rw [completedTfvdGreenLedgerSameSBoundary_seeded]
  simpa using
    (finiteCanonicalSeededTfvdBoundary_sub_provenance_eq_genuineGreenForm
      1 (kappa := tfvdHaarScale) tfvdHaarScale_ne_zero
      (fun _ : ℕ => (1 : ℂ)) (by intro m; norm_num) s)

end

end NativeCarryC3Crosswalk
