import NativeCarryC3Crosswalk.CompletedTfvdNaimarkFeasibility
import NativeCarryC3Crosswalk.GenuineBracketGreenIdentity
import NativeCarryC3Crosswalk.RealifiedGammaGreenEnergy
import NativeCarryC3Crosswalk.FiniteC3CompletedGreenGate

/-!
# Completed TFVD ledger to the provenance-preserving C3 Green form

The completed same-edge source keeps the ordinary gradient state, its
logarithmic jet, and the later rank-one residual.  The Green boundary form is
already determined before that residual collapse: on one complete C3 block,
the ordinary and log-jet provenance cores recover the two adjacent same-edge
wedges exactly.

This module records that source-level identification and then applies the
existing finite TFVD--Green theorem.  It also reconstructs the complete C3
port from the ordinary provenance leg, packs that port faithfully into the
all-bases camera completion, and applies the existing source gamma-field Green
identity in intrinsic complex carry time.

No scalar residual is inverted, no Wronskian is identified with a raw Gram by
definition, and no zero or critical-line hypothesis is used in the source to
Green identities.
-/

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Infinite
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

/-- Complete C3 Green port reconstructed from the ordinary provenance leg of
a completed TFVD ledger.  The first leg applies the already fixed C3 block
multiplier before any scalar synthesis; the second leg keeps the horizontal
gradients themselves. -/
def completedTfvdGreenLedgerC3Port
    (s : ℂ) (ledger : CompletedTfvdGreenLedger) :
    FiniteC3GreenPortCarrier 3 :=
  (WithLp.toLp 2 (fun n : Fin 3 =>
      cpPhaseNormalizer 3 s * natDirichletTerm s 3 * ledger.1.1.2 n),
    WithLp.toLp 2 (fun n : Fin 3 => ledger.1.1.2 n))

/-- On the canonical one-block ledger, the reconstructed port is literally
the complete bracket-resolved C3 Green boundary pair. -/
theorem completedTfvdGreenLedgerC3Port_seeded
    (s : ℂ) :
    completedTfvdGreenLedgerC3Port s
        (seededCompletedTfvdGreenLedger 1 s) =
      finiteC3GenuineBracketGreenBoundaryPair 3 s := by
  rw [finiteC3GenuineBracketGreenBoundaryPair_eq_greenBoundaryPair]
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    funext n
    simp [completedTfvdGreenLedgerC3Port,
      seededCompletedTfvdGreenLedger,
      c2DirichletGradientPrefixCore_apply,
      phaseNormalizedCpBlockGradient,
      cpBlockGradient_eq_eigenvalue_mul, mul_assoc]
  · apply WithLp.ofLp_injective 2
    funext n
    simp [completedTfvdGreenLedgerC3Port,
      seededCompletedTfvdGreenLedger,
      c2DirichletGradientPrefixCore_apply]

/-- Camera-completion state obtained from the complete C3 port reconstructed
from the seeded completed TFVD ledger. -/
def seededCompletedTfvdGreenCameraState (s : ℂ) :
    RealifiedCameraComplexification :=
  c3SixCameraPacking
    (completedTfvdGreenLedgerC3Port s
      (seededCompletedTfvdGreenLedger 1 s))

/-- The ledger-derived camera state is exactly the faithful six-camera packing
of the canonical complete C3 boundary pair. -/
@[simp] theorem seededCompletedTfvdGreenCameraState_eq_canonical
    (s : ℂ) :
    seededCompletedTfvdGreenCameraState s =
      c3SixCameraPacking (finiteC3GenuineBracketGreenBoundaryPair 3 s) := by
  rw [seededCompletedTfvdGreenCameraState,
    completedTfvdGreenLedgerC3Port_seeded]

/-- The complete ledger-derived camera state is nonzero at every parameter in
the open Genuine strip. -/
theorem seededCompletedTfvdGreenCameraState_ne_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    seededCompletedTfvdGreenCameraState s ≠ 0 := by
  intro hzero
  have hport :
      completedTfvdGreenLedgerC3Port s
          (seededCompletedTfvdGreenLedger 1 s) = 0 := by
    apply c3SixCameraPacking_injective
    change c3SixCameraPacking
        (completedTfvdGreenLedgerC3Port s
          (seededCompletedTfvdGreenLedger 1 s)) = 0 at hzero
    simpa only [map_zero] using hzero
  rw [completedTfvdGreenLedgerC3Port_seeded] at hport
  exact finiteC3GenuineFullGreenEndpoint_ne_zero
    3 (by norm_num) hs hport

/-- Off the half-abscissa, intrinsic complex carry time is nonreal. -/
theorem carryComplexTimeOfParameter_im_ne_zero_of_re_ne_half
    {s : ℂ} (hoff : s.re ≠ (1 : ℝ) / 2) :
    (carryComplexTimeOfParameter s).im ≠ 0 := by
  rw [carryComplexTimeOfParameter_im]
  intro hzero
  apply hoff
  unfold criticalDisplacement at hzero
  linarith

/-- Defect vector obtained by feeding the complete ledger-derived camera state
to the canonical carry gamma field at the intrinsic complex carry time. -/
def seededCompletedTfvdCarryGammaState
    (s : ℂ) (hoff : s.re ≠ (1 : ℝ) / 2) :
    RealifiedNaimarkComplexification :=
  carryGammaSource (carryComplexTimeOfParameter s)
    (carryComplexTimeOfParameter_im_ne_zero_of_re_ne_half hoff)
    (seededCompletedTfvdGreenCameraState s)

/-- The gamma field does not collapse the nonzero complete state reconstructed
from the TFVD ledger. -/
theorem seededCompletedTfvdCarryGammaState_ne_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    seededCompletedTfvdCarryGammaState s hoff ≠ 0 := by
  intro hzero
  apply seededCompletedTfvdGreenCameraState_ne_zero hs
  apply carryGammaSource_injective
    (carryComplexTimeOfParameter s)
    (carryComplexTimeOfParameter_im_ne_zero_of_re_ne_half hoff)
  simpa [seededCompletedTfvdCarryGammaState] using hzero

/-- The positive gamma energy of the complete ledger-derived state is strictly
positive at every off-critical point of the open strip. -/
theorem seededCompletedTfvdCarryGammaEnergy_pos
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    0 <
      ‖(seededCompletedTfvdCarryGammaState s hoff).fst‖ ^ 2 +
        ‖(seededCompletedTfvdCarryGammaState s hoff).snd‖ ^ 2 := by
  have hstate := seededCompletedTfvdCarryGammaState_ne_zero hs hoff
  by_contra hnot
  have hle :
      ‖(seededCompletedTfvdCarryGammaState s hoff).fst‖ ^ 2 +
          ‖(seededCompletedTfvdCarryGammaState s hoff).snd‖ ^ 2 ≤ 0 :=
    le_of_not_gt hnot
  have hfstNorm :
      ‖(seededCompletedTfvdCarryGammaState s hoff).fst‖ = 0 := by
    nlinarith [sq_nonneg
      ‖(seededCompletedTfvdCarryGammaState s hoff).snd‖]
  have hsndNorm :
      ‖(seededCompletedTfvdCarryGammaState s hoff).snd‖ = 0 := by
    nlinarith [sq_nonneg
      ‖(seededCompletedTfvdCarryGammaState s hoff).fst‖]
  have hfst : (seededCompletedTfvdCarryGammaState s hoff).fst = 0 :=
    norm_eq_zero.mp hfstNorm
  have hsnd : (seededCompletedTfvdCarryGammaState s hoff).snd = 0 :=
    norm_eq_zero.mp hsndNorm
  apply hstate
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · simpa using hfst
  · simpa using hsnd

/-- Applying the already proved source-relation Green identity to the complete
ledger-derived camera state produces the exact linear carry-time coefficient
multiplying its strictly positive gamma energy. -/
theorem seededCompletedTfvdCarryGammaState_diagonal_green_identity
    {s : ℂ} (hoff : s.re ≠ (1 : ℝ) / 2) :
    let lambda := carryComplexTimeOfParameter s
    let hlambda : lambda.im ≠ 0 :=
      carryComplexTimeOfParameter_im_ne_zero_of_re_ne_half hoff
    let u := seededCompletedTfvdGreenCameraState s
    let gamma := seededCompletedTfvdCarryGammaState s hoff
    2 * lambda.im *
          (‖gamma.fst‖ ^ 2 + ‖gamma.snd‖ ^ 2) =
      greenForm
          ((allBasesCauchyBlock lambda hlambda u).snd, u.snd)
          ((allBasesCauchyBlock lambda hlambda u).fst, u.fst) -
        greenForm
          ((allBasesCauchyBlock lambda hlambda u).fst, u.fst)
          ((allBasesCauchyBlock lambda hlambda u).snd, u.snd) := by
  dsimp
  simpa [seededCompletedTfvdCarryGammaState] using
    (carryGammaSource_diagonal_green_identity
      (carryComplexTimeOfParameter s)
      (carryComplexTimeOfParameter_im_ne_zero_of_re_ne_half hoff)
      (seededCompletedTfvdGreenCameraState s))

end

end NativeCarryC3Crosswalk
