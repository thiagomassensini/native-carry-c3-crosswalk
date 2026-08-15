import NativeCarryC3Crosswalk.BranchGreenQuadraticCrosswalk
import NativeCarryC3Crosswalk.GenuineBracketGreenIdentity

/-!
# Structural carry--TFVD--Green defect principle

The causal order is fixed explicitly:

1. positional carry defines the quadratic branch defect;
2. TFVD supplies the exact telescoping boundary decomposition;
3. the Green form is a later readout of that same TFVD computation.

The squared Green-scale branch defect below is defined before asking whether
any Genuine or completed readout vanishes.  Lean proves that it vanishes
identically on the half-abscissa, is strictly positive away from it, and is
an orthogonal coordinate of the enriched completed port.  Hence a zero of
that completed port can only occur after the pre-existing geometric defect
has vanished; the zero does not select or create the equilibrium.

This statement concerns the enriched completed port.  It does not assert
that vanishing of the scalar Genuine coordinate alone annihilates its
independent structural coordinate.
-/

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary

noncomputable section

/-- The squared Green-scale positional defect.  It is defined before asking
whether any Genuine or completed readout vanishes. -/
def structuralCarryGreenDefectEnergy (p : ℕ) (s : ℂ) : ℝ :=
  (infiniteReflectedGreenEnergy s * branchDefect p s.re) ^ 2

/-- The C3 positional defect is not an unrelated coordinate appended after
TFVD.  At every finite cutoff it is exactly a positive transfer multiple of
the same bracket-resolved TFVD--Green form.  This identity is valid before
any zero, critical-line, tail, or isotropy condition is imposed. -/
theorem branchDefect_mul_finiteReflectedGradientPairing_eq_neg_transfer_mul_greenForm
    (M : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ((branchDefect 3 s.re : ℝ) : ℂ) *
        finiteReflectedGradientPairing M s =
      -((branchToGreenTransferCoefficient 3 s.re : ℝ) : ℂ) *
        greenForm
          (finiteC3GenuineBracketGreenBoundaryPair M s)
          (finiteC3GenuineBracketGreenBoundaryPair M
            (reflectedParameter s)) := by
  rw [branchDefect_eq_neg_transfer_mul_radialDifference
      3 (by norm_num) hs,
    greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_radialFactorization]
  push_cast
  ring

theorem structuralCarryGreenDefectEnergy_nonneg (p : ℕ) (s : ℂ) :
    0 ≤ structuralCarryGreenDefectEnergy p s := by
  exact sq_nonneg _

/-- Strict positivity of the Green energy prevents it from hiding a nonzero
positional branch defect. -/
theorem structuralCarryGreenDefectEnergy_eq_zero_iff_branchDefect
    (p : ℕ) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    structuralCarryGreenDefectEnergy p s = 0 ↔
      branchDefect p s.re = 0 := by
  unfold structuralCarryGreenDefectEnergy
  rw [pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)]
  exact mul_eq_zero_iff_left
    (ne_of_gt (infiniteReflectedGreenEnergy_pos hs))

/-- The structural defect vanishes exactly when the prior positional
geometry is compatible. -/
theorem structuralCarryGreenDefectEnergy_eq_zero_iff_compatible
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    structuralCarryGreenDefectEnergy p s = 0 ↔
      C3PositionalGeometryCompatible s.re := by
  rw [structuralCarryGreenDefectEnergy_eq_zero_iff_branchDefect p hs,
    c3PositionalGeometryCompatible_iff]
  constructor
  · intro hdefect
    have hcritical :=
      (branchDefect_eq_zero_iff_criticalDisplacement_eq_zero
        p hp hs.1).1 hdefect
    unfold criticalDisplacement at hcritical
    linarith
  · intro hhalf
    apply
      (branchDefect_eq_zero_iff_criticalDisplacement_eq_zero
        p hp hs.1).2
    unfold criticalDisplacement
    linarith

/-- Coordinate form: the structural defect has exactly the half-abscissa as
its zero locus. -/
theorem structuralCarryGreenDefectEnergy_eq_zero_iff_re_eq_half
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    structuralCarryGreenDefectEnergy p s = 0 ↔
      s.re = (1 : ℝ) / 2 := by
  rw [structuralCarryGreenDefectEnergy_eq_zero_iff_compatible p hp hs,
    c3PositionalGeometryCompatible_iff]

/-- On the equilibrium line the defect vanishes identically, independently
of phase time and without any zero hypothesis. -/
@[simp] theorem structuralCarryGreenDefectEnergy_criticalLine
    (p : ℕ) (hp : Nat.Prime p) (time : ℝ) :
    structuralCarryGreenDefectEnergy p ⟨(1 : ℝ) / 2, time⟩ = 0 := by
  unfold structuralCarryGreenDefectEnergy branchDefect
  rw [branchNormSq_half p hp]
  norm_num

/-- Away from equilibrium the structural defect is strictly positive.  This
contains no Genuine-zero hypothesis. -/
theorem structuralCarryGreenDefectEnergy_pos_of_re_ne_half
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    0 < structuralCarryGreenDefectEnergy p s := by
  have hne : structuralCarryGreenDefectEnergy p s ≠ 0 := by
    intro hzero
    exact hoff
      ((structuralCarryGreenDefectEnergy_eq_zero_iff_re_eq_half
        p hp hs).1 hzero)
  exact (lt_iff_le_and_ne).2
    ⟨structuralCarryGreenDefectEnergy_nonneg p s, Ne.symm hne⟩

theorem structuralCarryGreenDefectEnergy_pos_iff_re_ne_half
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    0 < structuralCarryGreenDefectEnergy p s ↔
      s.re ≠ (1 : ℝ) / 2 := by
  constructor
  · intro hpos hhalf
    have hzero :=
      (structuralCarryGreenDefectEnergy_eq_zero_iff_re_eq_half
        p hp hs).2 hhalf
    linarith
  · exact structuralCarryGreenDefectEnergy_pos_of_re_ne_half p hp hs

/-- The structural energy is literally the third orthogonal coordinate in
the enriched completed readout. -/
theorem structuralCarryGreenDefectEnergy_le_completedReadout_norm_sq
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (p : ℕ) (s : ℂ) :
    structuralCarryGreenDefectEnergy p s ≤
      ‖c3EnrichedTailBranchCompletedReadout M kappa omega p s‖ ^ 2 := by
  exact branchDefectGreenEnergy_sq_le_enrichedTailCompletedReadout_norm_sq
    M kappa omega p s

/-- At a scalar Genuine zero the two tail/TFVD coordinates disappear, so the
completed norm is *exactly* the pre-existing structural defect energy.  The
zero does not annihilate that energy; it merely exposes it as the only
remaining orthogonal coordinate. -/
theorem c3EnrichedTailBranchCompletedReadout_norm_sq_of_genuine_zero
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    (p : ℕ) {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    ‖c3EnrichedTailBranchCompletedReadout M kappa omega p s‖ ^ 2 =
      structuralCarryGreenDefectEnergy p s := by
  rw [c3EnrichedTailBranchCompletedReadout_norm_sq_eq_genuine_branch
    M hkappa omega homega p hs, hzero]
  simp [structuralCarryGreenDefectEnergy]

/-- Consequently, a hypothetical scalar Genuine zero away from the
half-abscissa leaves a strictly positive completed TFVD norm. -/
theorem c3EnrichedTailBranchCompletedReadout_norm_pos_of_genuine_zero_off_critical
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    0 < ‖c3EnrichedTailBranchCompletedReadout M kappa omega p s‖ := by
  have henergy : 0 < structuralCarryGreenDefectEnergy p s :=
    structuralCarryGreenDefectEnergy_pos_of_re_ne_half p hp hs hoff
  have hledger :=
    c3EnrichedTailBranchCompletedReadout_norm_sq_of_genuine_zero
      M hkappa omega homega p hs hzero
  have hnorm :
      0 ≤ ‖c3EnrichedTailBranchCompletedReadout M kappa omega p s‖ :=
    norm_nonneg _
  nlinarith

/-- Pointwise kernel statement after the scalar Genuine coordinate has
vanished: the completed TFVD port closes exactly at positional equilibrium. -/
theorem c3EnrichedTailBranchCompletedReadout_eq_zero_iff_re_eq_half_of_genuine_zero
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    c3EnrichedTailBranchCompletedReadout M kappa omega p s = 0 ↔
      s.re = (1 : ℝ) / 2 := by
  rw [c3EnrichedTailBranchCompletedReadout_eq_zero_iff_genuine_and_compatible
      M hkappa omega homega p hp hs,
    and_iff_right hzero,
    c3PositionalGeometryCompatible_iff]

/-- A zero of the enriched completed port cannot create equilibrium; it can
only occur after the pre-existing structural defect has vanished. -/
theorem completedReadout_zero_implies_structuralDefect_zero
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (p : ℕ) (s : ℂ)
    (hzero : c3EnrichedTailBranchCompletedReadout M kappa omega p s = 0) :
    structuralCarryGreenDefectEnergy p s = 0 := by
  have hle := structuralCarryGreenDefectEnergy_le_completedReadout_norm_sq
    M kappa omega p s
  rw [hzero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hle
  exact le_antisymm hle (structuralCarryGreenDefectEnergy_nonneg p s)

/-- Structural necessity in coordinate form: completed vanishing forces the
already-defined geometric equilibrium. -/
theorem completedReadout_zero_implies_re_eq_half
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : c3EnrichedTailBranchCompletedReadout M kappa omega p s = 0) :
    s.re = (1 : ℝ) / 2 := by
  apply (structuralCarryGreenDefectEnergy_eq_zero_iff_re_eq_half
    p hp hs).1
  exact completedReadout_zero_implies_structuralDefect_zero
    M kappa omega p s hzero

/-- Chronological capstone: the bracket form is already the TFVD diagonal,
while the later Green-scale energy merely detects the positional defect whose
zero locus was fixed before either zero predicate was considered. -/
theorem genuineBracket_tfvd_green_structuralDefect_capstone
    (M : ℕ) (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    (greenForm
        (finiteC3GenuineBracketGreenBoundaryPair M s)
        (finiteC3GenuineBracketGreenBoundaryPair M (reflectedParameter s)) =
      finiteTfvdCpGreenDiagonal 3 M s) ∧
    (structuralCarryGreenDefectEnergy p s = 0 ↔
      C3PositionalGeometryCompatible s.re) ∧
    (0 < structuralCarryGreenDefectEnergy p s ↔
      s.re ≠ (1 : ℝ) / 2) := by
  exact
    ⟨greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_tfvdDiagonal M s,
      structuralCarryGreenDefectEnergy_eq_zero_iff_compatible p hp hs,
      structuralCarryGreenDefectEnergy_pos_iff_re_ne_half p hp hs⟩

/-- Zero-side mechanism capstone.  Scalar Genuine vanishing removes exactly
the two tail/TFVD coordinates.  The remaining completed norm is the prior
structural Green defect, and closing that full port is equivalent to the
half-abscissa.  In particular, no scalar-to-completed implication is inserted
into the statement. -/
theorem genuineZero_tfvd_completedStructuralResidual_capstone
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    (greenForm
        (finiteC3GenuineBracketGreenBoundaryPair M s)
        (finiteC3GenuineBracketGreenBoundaryPair M
          (reflectedParameter s)) =
      finiteTfvdCpGreenDiagonal 3 M s) ∧
    (‖c3EnrichedTailBranchCompletedReadout M kappa omega p s‖ ^ 2 =
      structuralCarryGreenDefectEnergy p s) ∧
    (c3EnrichedTailBranchCompletedReadout M kappa omega p s = 0 ↔
      s.re = (1 : ℝ) / 2) := by
  exact
    ⟨greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_tfvdDiagonal M s,
      c3EnrichedTailBranchCompletedReadout_norm_sq_of_genuine_zero
        M hkappa omega homega p hs hzero,
      c3EnrichedTailBranchCompletedReadout_eq_zero_iff_re_eq_half_of_genuine_zero
        M hkappa omega homega p hp hs hzero⟩

end

end NativeCarryC3Crosswalk
