import Mathlib.Analysis.InnerProductSpace.ProdL2
import CPFormal.Analytic.CpNativeCarrySpectrumExhaustion
import NativeCarryC3Crosswalk.C3TwoVariableGreenGamma

/-!
# Completed Green--Wronskian algebra

This module isolates the algebraic part of the proposed completed
Green--gamma route.  It deliberately does not manufacture the analytic state
or assume global nonvanishing.

The product rule keeps the two completion channels orthogonal.  The sum rule
keeps every off-diagonal cross term visible.  The final theorem records the
precise remaining gate: a diagonal Green identity together with a nonzero
Hilbert state confines a Genuine zero to the half-abscissa without division
by the scalar boundary value and without a simplicity assumption.
-/

open scoped ComplexConjugate

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp

noncomputable section

/-- Division-free scalar Green numerator attached to a value channel `F` and
a companion channel `Psi`. -/
def scalarGreenWronskian (F Psi : ℂ → ℂ) (z w : ℂ) : ℂ :=
  Psi z * (starRingEnd ℂ) (F w) -
    F z * (starRingEnd ℂ) (Psi w)

/-- One polarized cross term between two distinct scalar channels. -/
def scalarGreenCrossWronskian
    (F Psi G Theta : ℂ → ℂ) (z w : ℂ) : ℂ :=
  Psi z * (starRingEnd ℂ) (G w) -
    F z * (starRingEnd ℂ) (Theta w)

/-- Product completion preserves the two diagonal Green channels exactly. -/
theorem scalarGreenWronskian_mul
    (A PsiA G PsiG : ℂ → ℂ) (z w : ℂ) :
    scalarGreenWronskian
        (fun u ↦ A u * G u)
        (fun u ↦ PsiA u * G u + A u * PsiG u) z w =
      G z * (starRingEnd ℂ) (G w) *
          scalarGreenWronskian A PsiA z w +
        A z * (starRingEnd ℂ) (A w) *
          scalarGreenWronskian G PsiG z w := by
  unfold scalarGreenWronskian
  simp only [map_add, map_mul]
  ring

/-- A scalar sum retains both diagonal Wronskians and both ordered cross
terms.  No provenance channel is discarded by early scalar synthesis. -/
theorem scalarGreenWronskian_sum
    (F Psi G Theta : ℂ → ℂ) (z w : ℂ) :
    scalarGreenWronskian
        (fun u ↦ F u + G u)
        (fun u ↦ Psi u + Theta u) z w =
      scalarGreenWronskian F Psi z w +
        scalarGreenCrossWronskian F Psi G Theta z w +
        scalarGreenCrossWronskian G Theta F Psi z w +
        scalarGreenWronskian G Theta z w := by
  unfold scalarGreenWronskian scalarGreenCrossWronskian
  simp only [map_add]
  ring

/-- Orthogonal two-channel state associated with a product completion
`F = A * G`. -/
def completedGreenState
    {HA HG : Type*}
    [NormedAddCommGroup HA] [InnerProductSpace ℂ HA]
    [NormedAddCommGroup HG] [InnerProductSpace ℂ HG]
    (A G : ℂ → ℂ) (a : ℂ → HA) (g : ℂ → HG) (z : ℂ) :
    WithLp 2 (HA × HG) :=
  WithLp.toLp 2 (G z • a z, A z • g z)

/-- The direct-sum state realizes the weighted sum of the component Gram
kernels, with the conjugation dictated by Lean's first inner-product slot. -/
theorem completedGreenState_inner
    {HA HG : Type*}
    [NormedAddCommGroup HA] [InnerProductSpace ℂ HA]
    [NormedAddCommGroup HG] [InnerProductSpace ℂ HG]
    (A G : ℂ → ℂ) (a : ℂ → HA) (g : ℂ → HG) (z w : ℂ) :
    inner ℂ
        (completedGreenState A G a g w)
        (completedGreenState A G a g z) =
      G z * (starRingEnd ℂ) (G w) * inner ℂ (a w) (a z) +
        A z * (starRingEnd ℂ) (A w) * inner ℂ (g w) (g z) := by
  rw [WithLp.prod_inner_apply]
  simp only [completedGreenState, WithLp.ofLp_toLp,
    inner_smul_left, inner_smul_right]
  ring

/-- Component Green identities combine into the completed product identity. -/
theorem scalarGreenWronskian_directSum
    {HA HG : Type*}
    [NormedAddCommGroup HA] [InnerProductSpace ℂ HA]
    [NormedAddCommGroup HG] [InnerProductSpace ℂ HG]
    (A PsiA G PsiG : ℂ → ℂ)
    (a : ℂ → HA) (g : ℂ → HG) (z w : ℂ)
    (hA : scalarGreenWronskian A PsiA z w =
      (z - (starRingEnd ℂ) w) * inner ℂ (a w) (a z))
    (hG : scalarGreenWronskian G PsiG z w =
      (z - (starRingEnd ℂ) w) * inner ℂ (g w) (g z)) :
    scalarGreenWronskian
        (fun u ↦ A u * G u)
        (fun u ↦ PsiA u * G u + A u * PsiG u) z w =
      (z - (starRingEnd ℂ) w) *
        inner ℂ
          (completedGreenState A G a g w)
          (completedGreenState A G a g z) := by
  rw [scalarGreenWronskian_mul, hA, hG,
    completedGreenState_inner]
  ring

/-- A nonzero first product channel makes the completed state nonzero. -/
theorem completedGreenState_ne_zero_of_left
    {HA HG : Type*}
    [NormedAddCommGroup HA] [InnerProductSpace ℂ HA]
    [NormedAddCommGroup HG] [InnerProductSpace ℂ HG]
    (A G : ℂ → ℂ) (a : ℂ → HA) (g : ℂ → HG) (z : ℂ)
    (hG : G z ≠ 0) (ha : a z ≠ 0) :
    completedGreenState A G a g z ≠ 0 := by
  intro hzero
  have hpair : (G z • a z, A z • g z) = 0 := by
    exact WithLp.toLp_eq_zero.mp hzero
  have hleft : G z • a z = 0 :=
    congrArg Prod.fst hpair
  rcases smul_eq_zero.mp hleft with hscalar | hstate
  · exact hG hscalar
  · exact ha hstate

/-- A nonzero second product channel makes the completed state nonzero. -/
theorem completedGreenState_ne_zero_of_right
    {HA HG : Type*}
    [NormedAddCommGroup HA] [InnerProductSpace ℂ HA]
    [NormedAddCommGroup HG] [InnerProductSpace ℂ HG]
    (A G : ℂ → ℂ) (a : ℂ → HA) (g : ℂ → HG) (z : ℂ)
    (hA : A z ≠ 0) (hg : g z ≠ 0) :
    completedGreenState A G a g z ≠ 0 := by
  intro hzero
  have hpair : (G z • a z, A z • g z) = 0 := by
    exact WithLp.toLp_eq_zero.mp hzero
  have hright : A z • g z = 0 :=
    congrArg Prod.snd hpair
  rcases smul_eq_zero.mp hright with hscalar | hstate
  · exact hA hscalar
  · exact hg hstate

/-- Diagonal Green identity plus a nonzero Hilbert state forces the spectral
parameter to equal its conjugate.  The proof never divides by `F z`. -/
theorem eq_star_of_scalarGreenWronskian_diagonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (F Psi : ℂ → ℂ) (f : ℂ → H) (z : ℂ)
    (hzero : F z = 0)
    (hstate : f z ≠ 0)
    (hgreen : scalarGreenWronskian F Psi z z =
      (z - (starRingEnd ℂ) z) * inner ℂ (f z) (f z)) :
    z = (starRingEnd ℂ) z := by
  have hwronskian : scalarGreenWronskian F Psi z z = 0 := by
    simp [scalarGreenWronskian, hzero]
  have hproduct :
      (z - (starRingEnd ℂ) z) * inner ℂ (f z) (f z) = 0 := by
    rw [← hgreen, hwronskian]
  have hinner : inner ℂ (f z) (f z) ≠ 0 := by
    intro hzeroInner
    exact hstate (inner_self_eq_zero.mp hzeroInner)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right hinner)

/-- Genuine scalar boundary value in the intrinsic complex carry-time
coordinate. -/
def genuineComplexTimeBoundaryValue (z : ℂ) : ℂ :=
  genuineContinuation (carryComplexTimeParameter z)

/-- Pointwise completed Green data confine a Genuine zero.  The Green identity
and state nondegeneracy remain explicit inputs; this theorem does not claim to
construct them. -/
theorem genuineZero_re_eq_half_of_completedGreenState
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Psi : ℂ → ℂ) (f : ℂ → H) {s : ℂ}
    (hzero : genuineContinuation s = 0)
    (hstate : f (carryComplexTimeOfParameter s) ≠ 0)
    (hgreen :
      scalarGreenWronskian genuineComplexTimeBoundaryValue Psi
          (carryComplexTimeOfParameter s) (carryComplexTimeOfParameter s) =
        (carryComplexTimeOfParameter s -
            (starRingEnd ℂ) (carryComplexTimeOfParameter s)) *
          inner ℂ
            (f (carryComplexTimeOfParameter s))
            (f (carryComplexTimeOfParameter s))) :
    s.re = (1 : ℝ) / 2 := by
  have hboundaryZero :
      genuineComplexTimeBoundaryValue (carryComplexTimeOfParameter s) = 0 := by
    simp [genuineComplexTimeBoundaryValue, hzero]
  have hrealTime :
      carryComplexTimeOfParameter s =
        (starRingEnd ℂ) (carryComplexTimeOfParameter s) :=
    eq_star_of_scalarGreenWronskian_diagonal
      genuineComplexTimeBoundaryValue Psi f
      (carryComplexTimeOfParameter s) hboundaryZero hstate hgreen
  have him : (carryComplexTimeOfParameter s).im = 0 :=
    Complex.conj_eq_iff_im.mp hrealTime.symm
  rw [carryComplexTimeOfParameter_im] at him
  unfold criticalDisplacement at him
  linarith

/-- Strip-wide confinement follows once the completed Green identity and the
nonzero state are constructed uniformly in complex carry time. -/
theorem finalGenuineZeroConfinement_of_completedGreenState
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Psi : ℂ → ℂ) (f : ℂ → H)
    (hstate : ∀ z, f z ≠ 0)
    (hgreen : ∀ z,
      scalarGreenWronskian genuineComplexTimeBoundaryValue Psi z z =
        (z - (starRingEnd ℂ) z) * inner ℂ (f z) (f z)) :
    ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
      genuineContinuation s = 0 →
        s.re = (1 : ℝ) / 2 := by
  intro s _hs hzero
  exact genuineZero_re_eq_half_of_completedGreenState
    Psi f hzero (hstate (carryComplexTimeOfParameter s))
      (hgreen (carryComplexTimeOfParameter s))

end

end NativeCarryC3Crosswalk
