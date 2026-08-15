import CarryGeometry.QuadraticAmplitude
import CPFormal.Analytic.CpGenuineNativeRealBoundaryCrosswalk
import CPFormal.Analytic.CpGenuineGreenKernelInclusion
import CPFormal.Analytic.CpNativeCarryRealSpectralBoundaryCarrier

/-!
# C3 zero and foundational positional compatibility

This module implements the three-step audit suggested by the foundational
`carry-geometry` library.

1. `C3PositionalGeometryCompatible` is defined without mentioning the
   half-abscissa.  It says only that the C3 deformed amplitude reproduces the
   positional carry mass at every positive depth.
2. The foundational rigidity theorem proves that this compatibility holds
   exactly at `sigma = 1 / 2`.
3. The remaining statement is isolated as
   `C3OperatorZerosPreservePositionalGeometryInStrip`: raw C3 boundary closure
   should imply that prior geometric compatibility.

No instance of step 3 is declared.  Instead, Lean proves that it is exactly
the already identified boundary-mass preservation gate, exactly native
zero-rigidity, and exactly strong Genuine nonvanishing in the open strip.
Thus the decomposition shortens the capstone and identifies the missing
arrow without inserting its conclusion into the definition of a zero.
-/

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp

noncomputable section

/-! ## Step 1: compatibility without a critical-line clause -/

/-- Foundational geometric compatibility for the C3 positional base.  The
definition contains only equality between the deformed quadratic amplitude
and carry mass at every positive depth. -/
def C3PositionalGeometryCompatible (sigma : ℝ) : Prop :=
  CarryGeometry.PositionalMassCompatible 3 sigma

/-! ## Step 2: the purely geometric rigidity theorem -/

/-- The foundational carry geometry has one and only one compatible radial
exponent.  This theorem contains no operator-zero or Genuine hypothesis. -/
theorem c3PositionalGeometryCompatible_iff
    (sigma : ℝ) :
    C3PositionalGeometryCompatible sigma ↔
      sigma = (1 : ℝ) / 2 := by
  exact CarryGeometry.positionalMassCompatible_iff
    3 (by norm_num) sigma

/-- The minimal foundational predicate and the existing native real-plane
mass predicate are the same geometric domain.  Their pointwise formulae are
different, but both are independently rigid at the same exponent. -/
theorem c3PositionalGeometryCompatible_iff_nativeRealPlaneMassCompatible
    (sigma time : ℝ) :
    C3PositionalGeometryCompatible sigma ↔
      NativeCarryRealPlaneMassCompatible sigma time := by
  rw [c3PositionalGeometryCompatible_iff,
    nativeCarryRealPlaneMassCompatible_iff]

/-! ## Step 3: the only new transport obligation -/

/-- The exact missing lemma, stated globally on the analytic strip: a raw C3
operator zero preserves the positional quadratic geometry that existed before
the operator was defined.  The definition does not mention `sigma = 1 / 2`. -/
def C3OperatorZerosPreservePositionalGeometryInStrip : Prop :=
  ∀ {sigma time : ℝ}, 0 < sigma → sigma < 1 →
    IsNativeCarryRealOperatorZero 3 sigma time →
      C3PositionalGeometryCompatible sigma

/-- Pointwise scope guard.  At a fixed strip parameter, the desired third
lemma is literally the implication from a Genuine zero to the half-abscissa.
This is an equivalence of propositions, not an assumption in either
direction. -/
theorem c3OperatorZero_implies_positionalCompatibility_iff_pointwise_zeroRigidity
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    (IsNativeCarryRealOperatorZero 3 s.re s.im →
        C3PositionalGeometryCompatible s.re) ↔
      (genuineContinuation s = 0 →
        s.re = (1 : ℝ) / 2) := by
  rw [isNativeCarryRealOperatorZero_iff,
    nativeCarryRealBoundaryClosure_iff_genuineContinuation_zero hs,
    c3PositionalGeometryCompatible_iff]

/-- Rephrasing the third lemma with the foundational predicate does not
change its mathematical content: it is exactly the existing raw-boundary to
native-mass preservation obligation. -/
theorem c3OperatorZerosPreservePositionalGeometryInStrip_iff_boundaryClosurePreservesMass :
    C3OperatorZerosPreservePositionalGeometryInStrip ↔
      NativeCarryRealPlaneBoundaryClosurePreservesMass := by
  constructor
  · intro hgeometry sigma time hsigma0 hsigma1 hclose
    have hzero : IsNativeCarryRealOperatorZero 3 sigma time :=
      (isNativeCarryRealOperatorZero_three_iff sigma time).2 hclose
    exact
      (c3PositionalGeometryCompatible_iff_nativeRealPlaneMassCompatible
        sigma time).1
        (hgeometry hsigma0 hsigma1 hzero)
  · intro hmass sigma time hsigma0 hsigma1 hzero
    have hclose : NativeCarryRealPlaneBoundaryClosesAt sigma time :=
      (isNativeCarryRealOperatorZero_three_iff sigma time).1 hzero
    exact
      (c3PositionalGeometryCompatible_iff_nativeRealPlaneMassCompatible
        sigma time).2
        (hmass hsigma0 hsigma1 hclose)

/-- The foundational formulation is also exactly the native real-plane
zero-rigidity gate already isolated by the Green carrier audit. -/
theorem c3OperatorZerosPreservePositionalGeometryInStrip_iff_nativeZeroRigidity :
    C3OperatorZerosPreservePositionalGeometryInStrip ↔
      NativeCarryRealPlaneZeroRigidity := by
  rw [
    c3OperatorZerosPreservePositionalGeometryInStrip_iff_boundaryClosurePreservesMass,
    nativeCarryRealPlaneBoundaryClosurePreservesMass_iff_zeroRigidity]

/-- Global scope guard: proving step 3 for every C3 zero in the strip has
exactly the strength of strong Genuine nonvanishing there.  Hence none of the
first two foundational lemmas can discharge step 3 by themselves. -/
theorem c3OperatorZerosPreservePositionalGeometryInStrip_iff_strongNonvanishing :
    C3OperatorZerosPreservePositionalGeometryInStrip ↔
      GenuineStrongNonvanishingInStrip := by
  constructor
  · intro hgeometry s hs hoff hzero
    have hnative : IsNativeCarryRealOperatorZero 3 s.re s.im := by
      rw [isNativeCarryRealOperatorZero_iff,
        nativeCarryRealBoundaryClosure_iff_genuineContinuation_zero hs]
      exact hzero
    have hcompatible : C3PositionalGeometryCompatible s.re :=
      hgeometry hs.1 hs.2 hnative
    exact hoff
      ((c3PositionalGeometryCompatible_iff s.re).1 hcompatible)
  · intro hstrong sigma time hsigma0 hsigma1 hzero
    apply (c3PositionalGeometryCompatible_iff sigma).2
    by_contra hoff
    let s : ℂ := ⟨sigma, time⟩
    have hs : s ∈ genuineCriticalStrip := by
      exact ⟨hsigma0, hsigma1⟩
    have hnative : IsNativeCarryRealOperatorZero 3 s.re s.im := by
      simpa [s] using hzero
    have hgenuine : genuineContinuation s = 0 := by
      rw [← nativeCarryRealBoundaryClosure_iff_genuineContinuation_zero hs,
        ← isNativeCarryRealOperatorZero_iff]
      exact hnative
    have hoff' : s.re ≠ (1 : ℝ) / 2 := by
      simpa [s] using hoff
    exact (hstrong hs hoff') hgenuine

/-- The clean conditional capstone.  Once and only once the new transport
lemma is supplied, a C3 zero inherits compatibility and the foundational
rigidity theorem returns the critical exponent. -/
theorem c3OperatorZero_positionalCompatibility_capstone
    (htransport : C3OperatorZerosPreservePositionalGeometryInStrip)
    {sigma time : ℝ} (hsigma0 : 0 < sigma) (hsigma1 : sigma < 1)
    (hzero : IsNativeCarryRealOperatorZero 3 sigma time) :
    C3PositionalGeometryCompatible sigma ∧
      sigma = (1 : ℝ) / 2 := by
  have hcompatible := htransport hsigma0 hsigma1 hzero
  exact ⟨hcompatible,
    (c3PositionalGeometryCompatible_iff sigma).1 hcompatible⟩

end

end NativeCarryC3Crosswalk
