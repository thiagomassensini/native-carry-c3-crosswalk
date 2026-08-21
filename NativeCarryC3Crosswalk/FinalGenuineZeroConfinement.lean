import NativeCarryC3Crosswalk.FiniteC3CompletedGreenGate
import NativeCarryC3Crosswalk.StructuralTfvdGreenDefect
import NativeCarryC3Crosswalk.CanonicalStateTraceClosure
import NativeCarryC3Crosswalk.BracketGlobalRelationalLaw

/-!
# Kernel diagnostic for global Genuine-zero confinement

The parent commit asked the Lean kernel for the final theorem with no new
structure, activation predicate, positivity hypothesis, zero list, or
confinement field.  GitHub CI run `32449877433` compiled the complete public
theorem graph and stopped at one equation: the completed scalar Wronskian must
be the linear carry-time factor times the raw C3 gradient Gram.

This module records that literal equation as an interface and proves that it
is sufficient.  It does not claim the interface unconditionally.  In
particular, the finite C3 state's nondegeneracy is already a theorem; the
remaining analytic construction is the completed Green--Wronskian identity,
not self-adjointness or cutoff control.
-/

open scoped ComplexConjugate

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp

noncomputable section

/-- Canonical division-free companion of the completed Genuine boundary
value in intrinsic complex carry time. -/
def genuineComplexTimeLogJet (z : ℂ) : ℂ :=
  -deriv genuineComplexTimeBoundaryValue z

/-- The unconditional global confinement statement, with no bundled
realization or activation premise. -/
def FinalGenuineZeroConfinement : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    genuineContinuation s = 0 →
      s.re = (1 : ℝ) / 2

/-- The exact residual equation reported by the unconditional CI probe after
all algebraic, cutoff, trace, structural-defect, and finite-state rewrites.
This is an interface declaration, not a proved theorem. -/
def FiniteC3CompletedGreenWronskianSeam (M : ℕ) : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    s.re ≠ (1 : ℝ) / 2 →
      scalarGreenWronskian
          genuineComplexTimeBoundaryValue genuineComplexTimeLogJet
          (carryComplexTimeOfParameter s) (carryComplexTimeOfParameter s) =
        (carryComplexTimeOfParameter s -
            (starRingEnd ℂ) (carryComplexTimeOfParameter s)) *
          c3RawGammaGram M s s

/-- The CI-isolated seam, together with the already proved nondegeneracy of
the finite C3 gradient state, is sufficient for unconditional confinement. -/
theorem finalGenuineZeroConfinement_of_finiteC3CompletedGreenWronskianSeam
    (M : ℕ) (hM : 0 < M)
    (hseam : FiniteC3CompletedGreenWronskianSeam M) :
    FinalGenuineZeroConfinement := by
  unfold FinalGenuineZeroConfinement
  apply finalGenuineZeroConfinement_of_finiteC3GradientGreenWronskian
    M hM genuineComplexTimeLogJet
  intro s hs hoff
  rw [inner_finiteC3CarryTimeGradientState]
  simp only [carryComplexTimeParameter_ofParameter]
  exact hseam hs hoff

end

end NativeCarryC3Crosswalk
