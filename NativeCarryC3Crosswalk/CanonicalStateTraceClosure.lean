import NativeCarryC3Crosswalk.StructuralTfvdGreenDefect
import NativeCarryC3Crosswalk.ArithmeticNonlocalTrace
import CPFormal.Analytic.CpGenuineSimpleRootCarryState

/-!
# Canonical-state trace closure

This module identifies the exact state-specific regularity statement behind
closure of the enriched C3 TFVD port.  It introduces no new zero predicate,
Green operator, selected inverse, or confinement assumption.

At a scalar Genuine zero, the completed port closes exactly when the
canonical mass endpoint belongs to the explicit domain of the closed
arithmetic nonlocal trace.  For a multiplicity-one zero, the same condition
is exactly simultaneous square summability of the material traces of the
already constructed global root-tangent mass state.

Thus the remaining implication is no longer phrased as a scalar kernel
transport.  It is the concrete analytic regularity assertion that the
canonical arithmetic state lies in a known proper dense domain.
-/

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp

noncomputable section

/-- Before any zero is mentioned, vanishing of the structural carry--Green
defect is exactly admissibility of the canonical mass endpoint for the
closed arithmetic nonlocal trace.  This identifies the same half-amplitude
regularity on the geometric and operator-domain sides without assuming it. -/
theorem structuralCarryGreenDefectEnergy_eq_zero_iff_massState_mem_traceDomain
    (traceCutoff : ℕ) (htraceCutoff : 0 < traceCutoff)
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    structuralCarryGreenDefectEnergy p s = 0 ↔
      primeMassGreenBulkState traceCutoff s hs ∈
        arithmeticNonlocalTrace.domain := by
  rw [structuralCarryGreenDefectEnergy_eq_zero_iff_re_eq_half p hp hs,
    primeMassGreenBulkState_mem_arithmeticNonlocalTrace_domain_iff
      traceCutoff htraceCutoff hs]
  unfold criticalDisplacement
  constructor <;> intro h <;> linarith

/-- At a Genuine zero, closing the enriched TFVD port is exactly membership
of the canonical mass state in the maximal domain of the closed arithmetic
nonlocal trace.  The two cutoffs need not agree because the tail coordinate
is cutoff invariant. -/
theorem c3EnrichedTailBranchCompletedReadout_eq_zero_iff_massState_mem_traceDomain
    (tailCutoff traceCutoff : ℕ) (htraceCutoff : 0 < traceCutoff)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    c3EnrichedTailBranchCompletedReadout
        tailCutoff kappa omega p s = 0 ↔
      primeMassGreenBulkState traceCutoff s hs ∈
        arithmeticNonlocalTrace.domain := by
  rw [c3EnrichedTailBranchCompletedReadout_eq_zero_iff_re_eq_half_of_genuine_zero
      tailCutoff hkappa omega homega p hp hs hzero,
    primeMassGreenBulkState_mem_arithmeticNonlocalTrace_domain_iff
      traceCutoff htraceCutoff hs]
  unfold criticalDisplacement
  constructor <;> intro h <;> linarith

/-- The same bridge in coercive form: at a Genuine zero, the completed norm
is positive exactly when the canonical mass state is outside the nonlocal
trace domain. -/
theorem c3EnrichedTailBranchCompletedReadout_norm_pos_iff_massState_not_mem_traceDomain
    (tailCutoff traceCutoff : ℕ) (htraceCutoff : 0 < traceCutoff)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    0 < ‖c3EnrichedTailBranchCompletedReadout
        tailCutoff kappa omega p s‖ ↔
      primeMassGreenBulkState traceCutoff s hs ∉
        arithmeticNonlocalTrace.domain := by
  rw [norm_pos_iff]
  exact not_congr
    (c3EnrichedTailBranchCompletedReadout_eq_zero_iff_massState_mem_traceDomain
      tailCutoff traceCutoff htraceCutoff hkappa omega homega p hp hs hzero)

/-- For a simple Genuine root, the scalar mass-state domain and the material
vertical-trace domain of the global root-tangent state are literally the same
regularity condition. -/
theorem massState_mem_traceDomain_iff_simpleRoot_globalTraceDomain
    (traceCutoff : ℕ) (htraceCutoff : 0 < traceCutoff)
    {s : ℂ} (hroot : IsSimpleGenuineZeroInStrip s) :
    primeMassGreenBulkState traceCutoff s hroot.1 ∈
        arithmeticNonlocalTrace.domain ↔
      SimpleRootMassVerticalGlobalTraceDomainAt
        traceCutoff s hroot := by
  rw [primeMassGreenBulkState_mem_arithmeticNonlocalTrace_domain_iff
      traceCutoff htraceCutoff hroot.1,
    simpleRootMassVerticalGlobalTraceDomainAt_iff
      traceCutoff htraceCutoff hroot]

/-- State-specific version of the final gate for a multiplicity-one root.
The completed C3 port closes exactly when the global mass state constructed
from the root tangents has square-summable material trace over all primes. -/
theorem c3EnrichedTailBranchCompletedReadout_eq_zero_iff_simpleRoot_globalTraceDomain
    (tailCutoff traceCutoff : ℕ) (htraceCutoff : 0 < traceCutoff)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hroot : IsSimpleGenuineZeroInStrip s) :
    c3EnrichedTailBranchCompletedReadout
        tailCutoff kappa omega p s = 0 ↔
      SimpleRootMassVerticalGlobalTraceDomainAt
        traceCutoff s hroot := by
  rw [c3EnrichedTailBranchCompletedReadout_eq_zero_iff_massState_mem_traceDomain
      tailCutoff traceCutoff htraceCutoff hkappa omega homega p hp
      hroot.1 hroot.2.1,
    massState_mem_traceDomain_iff_simpleRoot_globalTraceDomain
      traceCutoff htraceCutoff hroot]

/-- Simple-root capstone for the canonical-state mechanism.  Scalar
vanishing exposes the structural energy; port closure is then exactly the
global material-trace regularity of the root-derived canonical state. -/
theorem simpleGenuineRoot_completedPort_traceClosure_capstone
    (tailCutoff traceCutoff : ℕ) (htraceCutoff : 0 < traceCutoff)
    {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hroot : IsSimpleGenuineZeroInStrip s) :
    (‖c3EnrichedTailBranchCompletedReadout
        tailCutoff kappa omega p s‖ ^ 2 =
      structuralCarryGreenDefectEnergy p s) ∧
    (c3EnrichedTailBranchCompletedReadout
        tailCutoff kappa omega p s = 0 ↔
      SimpleRootMassVerticalGlobalTraceDomainAt
        traceCutoff s hroot) := by
  exact
    ⟨c3EnrichedTailBranchCompletedReadout_norm_sq_of_genuine_zero
        tailCutoff hkappa omega homega p hroot.1 hroot.2.1,
      c3EnrichedTailBranchCompletedReadout_eq_zero_iff_simpleRoot_globalTraceDomain
        tailCutoff traceCutoff htraceCutoff hkappa omega homega p hp hroot⟩

end

end NativeCarryC3Crosswalk
