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

end

end NativeCarryC3Crosswalk
