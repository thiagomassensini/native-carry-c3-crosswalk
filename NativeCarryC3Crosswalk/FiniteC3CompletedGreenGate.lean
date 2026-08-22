import NativeCarryC3Crosswalk.CompletedGreenWronskian
import NativeCarryC3Crosswalk.FullEndpointPoissonDefect

/-!
# Finite C3 state for the completed Green gate

The horizontal-gradient coordinate of the full provenance-preserving C3 port
is a genuine complex Hilbert state.  At every nonempty cutoff in the open
Genuine strip it is nonzero, independently of scalar vanishing and root
multiplicity.

Using this state discharges the nondegeneracy half of the completed
Green--Wronskian gate.  The sole remaining input to the capstone below is the
linear-parameter Green identity itself.  The existing raw C3 theorem has a
different eigenvalue coefficient, so that input is not inferred here.
-/

open scoped ComplexConjugate

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp

noncomputable section

/-- Horizontal-gradient Hilbert state carried by the finite full C3 port in
intrinsic complex carry time. -/
def finiteC3CarryTimeGradientState (M : ℕ) (z : ℂ) :
    FiniteC3GreenBoundarySpace M :=
  (finiteC3GenuineBracketGreenBoundaryPair M
    (carryComplexTimeParameter z)).2

@[simp] theorem finiteC3CarryTimeGradientState_apply
    (M : ℕ) (z : ℂ) (n : Fin M) :
    finiteC3CarryTimeGradientState M z n =
      positiveDirichletGradient (carryComplexTimeParameter z) n :=
  rfl

/-- The horizontal-gradient coordinate itself is nonzero at every nonempty
cutoff in the Genuine strip. -/
theorem finiteC3GenuineGradientState_ne_zero
    (M : ℕ) (hM : 0 < M)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    (finiteC3GenuineBracketGreenBoundaryPair M s).2 ≠ 0 := by
  intro hzero
  have hpairZero : finiteReflectedGradientPairing M s = 0 := by
    unfold finiteReflectedGradientPairing
    apply Finset.sum_eq_zero
    intro n hn
    have hnlt : n < M := Finset.mem_range.mp hn
    have hcoordinate := congrArg
      (fun v : FiniteC3GreenBoundarySpace M => v ⟨n, hnlt⟩) hzero
    simp only [finiteC3GenuineBracketGreenBoundaryPair_snd_apply,
      PiLp.zero_apply] at hcoordinate
    rw [hcoordinate]
    simp
  exact (finiteReflectedGradientPairing_ne_zero hM hs) hpairZero

/-- Carry-time spelling of the nondegenerate finite C3 gradient state. -/
theorem finiteC3CarryTimeGradientState_ne_zero
    (M : ℕ) (hM : 0 < M)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    finiteC3CarryTimeGradientState M (carryComplexTimeOfParameter s) ≠ 0 := by
  simpa [finiteC3CarryTimeGradientState] using
    finiteC3GenuineGradientState_ne_zero M hM hs

/-- The raw C3 Gram kernel is literally the Hilbert Gram of the finite
carry-time gradient state. -/
theorem inner_finiteC3CarryTimeGradientState
    (M : ℕ) (w z : ℂ) :
    inner ℂ
        (finiteC3CarryTimeGradientState M w)
        (finiteC3CarryTimeGradientState M z) =
      c3RawGammaGram M
        (carryComplexTimeParameter w)
        (carryComplexTimeParameter z) := by
  rw [PiLp.inner_apply]
  simp only [finiteC3CarryTimeGradientState,
    finiteC3GenuineBracketGreenBoundaryPair_snd_apply,
    RCLike.inner_apply']
  rw [Finset.sum_fin_eq_sum_range]
  unfold c3RawGammaGram
  apply Finset.sum_congr rfl
  intro n hn
  have hlt : n < M := Finset.mem_range.mp hn
  simp only [hlt, dite_true]

/-- With the canonical finite C3 gradient state, nondegeneracy is already a
theorem.  Therefore a completed diagonal Green--Wronskian identity is the
only remaining premise needed for global Genuine zero confinement. -/
theorem finalGenuineZeroConfinement_of_finiteC3GradientGreenWronskian
    (M : ℕ) (hM : 0 < M) (Psi : ℂ → ℂ)
    (hgreen : ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
      s.re ≠ (1 : ℝ) / 2 →
      scalarGreenWronskian genuineComplexTimeBoundaryValue Psi
          (carryComplexTimeOfParameter s) (carryComplexTimeOfParameter s) =
        (carryComplexTimeOfParameter s -
            (starRingEnd ℂ) (carryComplexTimeOfParameter s)) *
          inner ℂ
            (finiteC3CarryTimeGradientState M
              (carryComplexTimeOfParameter s))
            (finiteC3CarryTimeGradientState M
              (carryComplexTimeOfParameter s))) :
    ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
      genuineContinuation s = 0 →
        s.re = (1 : ℝ) / 2 := by
  apply finalGenuineZeroConfinement_of_completedGreenState
    Psi (finiteC3CarryTimeGradientState M)
  · intro s hs _hoff
    exact finiteC3CarryTimeGradientState_ne_zero M hM hs
  · intro s hs hoff
    exact hgreen hs hoff

end

end NativeCarryC3Crosswalk
