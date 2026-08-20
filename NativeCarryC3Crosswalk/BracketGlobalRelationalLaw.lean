import NativeCarryC3Crosswalk.FinitePackaging
import NativeCarryC3Crosswalk.GenuineBracketGreenFactorization
import NativeCarryC3Crosswalk.EnrichedTfvdPairTailClosure
import NativeCarryC3Crosswalk.StructuralTfvdGreenDefect
import NativeCarryC3Crosswalk.ArithmeticNonlocalTrace

/-!
# Global relational law of the bracket

This module packages the invariant that survives the native real, analytic
bracket, Genuine, TFVD, Green, and arithmetic-trace presentations.

Two bracket readouts are kept distinct.

* The scalar bracket chart factors through the Genuine continuation, so a
  Genuine zero annihilates that scalar value.
* The reflected Green bracket factors as radial tilt times a nonzero reflected
  pairing, so closure of that form detects exactly the half-abscissa.

The closed arithmetic trace supplies the operator-domain presentation of the
same condition. Pointwise, trace-domain admissibility, Green-bracket closure,
zero structural defect energy, and vanishing tilt are equivalent. Globally,
asking every Genuine zero to activate any one of those conditions is equivalent
to the existing strong-nonvanishing frontier.

No implication from scalar bracket vanishing to Green-bracket closure is
assumed. The final capstone is an equivalence law between presentations, not
an insertion of the confinement statement as a hidden hypothesis.
-/

open scoped Topology

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary
open NativeCarrySpectralWeyl.Camera
open Filter

noncomputable section

/-- One finite capstone for the common bracket computation. The first
coordinate equality is the native real/complex packaging. The remaining
equalities identify the differentiated Genuine bracket with its oriented
Genuine flux, TFVD diagonal, and radial Green factorization. No zero, strip,
limit, or equilibrium hypothesis occurs. -/
theorem finiteNativeGenuineTfvdGreenBracketLaw
    (time : ℝ) (camera nativeCutoff greenCutoff : ℕ) (s : ℂ) :
    (CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
        (FiniteNativeCarryOperator.Operator.finiteNativeOperator
          camera nativeCutoff time) =
      finiteBracketCharacteristic camera nativeCutoff (nativeLine time)) ∧
    (greenForm (𝕜 := ℂ)
        (finiteC3GenuineBracketGreenBoundaryPair greenCutoff s)
        (finiteC3GenuineBracketGreenBoundaryPair greenCutoff
          (reflectedParameter s)) =
      finiteOrientedGenuineCpGreenFlux 3 greenCutoff s) ∧
    (greenForm (𝕜 := ℂ)
        (finiteC3GenuineBracketGreenBoundaryPair greenCutoff s)
        (finiteC3GenuineBracketGreenBoundaryPair greenCutoff
          (reflectedParameter s)) =
      finiteTfvdCpGreenDiagonal 3 greenCutoff s) ∧
    (greenForm (𝕜 := ℂ)
        (finiteC3GenuineBracketGreenBoundaryPair greenCutoff s)
        (finiteC3GenuineBracketGreenBoundaryPair greenCutoff
          (reflectedParameter s)) =
      ((cpRadialDifference 3
        (criticalDisplacement s.re) : ℝ) : ℂ) *
        finiteReflectedGradientPairing greenCutoff s) := by
  exact
    ⟨packaged_finiteNativeOperator_eq_finiteBracketCharacteristic
        time camera nativeCutoff,
      greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_genuineFlux
        greenCutoff s,
      greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_tfvdDiagonal
        greenCutoff s,
      greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_radialFactorization
        greenCutoff s⟩

/-- Closure of the concrete differentiated Genuine bracket in the reflected
Green form. This definition contains no zero predicate. -/
def C3GenuineBracketGreenClosesAt (s : ℂ) : Prop :=
  Tendsto
    (fun M : ℕ ↦
      greenForm (𝕜 := ℂ)
        (finiteC3GenuineBracketGreenBoundaryPair M s)
        (finiteC3GenuineBracketGreenBoundaryPair M
          (reflectedParameter s)))
    atTop (nhds 0)

/-- A Genuine zero annihilates the scalar bracket chart exactly. This is the
value coordinate and is deliberately kept separate from Green-form closure. -/
theorem genuineZero_scalarBracketChart_eq_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    bracketedDirichletChart 3 s = 0 := by
  rw [bracketedDirichletChart_eq_cpChartFactor_mul_genuineContinuation
      3 (by norm_num) (by norm_num) hs,
    hzero, mul_zero]

/-- The Green bracket is the tilt detector: it closes exactly on the
half-abscissa because the reflected pairing has nonzero limit in the strip. -/
theorem c3GenuineBracketGreenClosesAt_iff_re_eq_half
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    C3GenuineBracketGreenClosesAt s ↔
      s.re = (1 : ℝ) / 2 := by
  simpa [C3GenuineBracketGreenClosesAt] using
    greenForm_finiteC3GenuineBracketGreenBoundaryPair_tendsto_zero_iff hs

/-- The maximal domain of the closed arithmetic trace and closure of the
concrete Green bracket are two presentations of the same pointwise condition.
No Genuine-zero hypothesis is needed. -/
theorem primeMassGreenBulkState_mem_traceDomain_iff_c3GenuineBracketGreenClosesAt
    (traceCutoff : ℕ) (htraceCutoff : 0 < traceCutoff)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    primeMassGreenBulkState traceCutoff s hs ∈
        arithmeticNonlocalTrace.domain ↔
      C3GenuineBracketGreenClosesAt s := by
  rw [primeMassGreenBulkState_mem_arithmeticNonlocalTrace_domain_iff
      traceCutoff htraceCutoff hs,
    c3GenuineBracketGreenClosesAt_iff_re_eq_half hs]
  unfold criticalDisplacement
  constructor <;> intro h <;> linarith

/-- Vanishing of the positive structural carry--Green defect and Green-bracket
closure have exactly the same locus. -/
theorem structuralCarryGreenDefectEnergy_eq_zero_iff_c3GenuineBracketGreenClosesAt
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    structuralCarryGreenDefectEnergy p s = 0 ↔
      C3GenuineBracketGreenClosesAt s := by
  rw [structuralCarryGreenDefectEnergy_eq_zero_iff_re_eq_half p hp hs,
    c3GenuineBracketGreenClosesAt_iff_re_eq_half hs]

/-- Whenever the canonical mass state is admissible for the closed trace, its
canonical boundary port belongs to the fixed maximal Green-isotropic relation
and the concrete differentiated bracket closes. This is the operator-side
realization of the bracket law. -/
theorem canonicalMassTraceDomain_realizesBracketLaw
    (traceCutoff : ℕ) (htraceCutoff : 0 < traceCutoff)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hdomain : primeMassGreenBulkState traceCutoff s hs ∈
      arithmeticNonlocalTrace.domain) :
    arithmeticNonlocalBoundaryPort
        ⟨primeMassGreenBulkState traceCutoff s hs, hdomain⟩ ∈
          arithmeticNonlocalBoundaryRelation ∧
      C3GenuineBracketGreenClosesAt s := by
  exact
    ⟨arithmeticNonlocalBoundaryPort_mem_relation
        ⟨primeMassGreenBulkState traceCutoff s hs, hdomain⟩,
      (primeMassGreenBulkState_mem_traceDomain_iff_c3GenuineBracketGreenClosesAt
        traceCutoff htraceCutoff hs).1 hdomain⟩

/-- Pointwise law at a Genuine zero. The scalar bracket value is zero, while
closure of the Green bracket is equivalent both to operator-domain
admissibility and to zero tilt. The theorem does not infer those equivalent
conditions from scalar cancellation. -/
theorem genuineZero_bracketRelationalLaw
    (traceCutoff : ℕ) (htraceCutoff : 0 < traceCutoff)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    (bracketedDirichletChart 3 s = 0) ∧
    (primeMassGreenBulkState traceCutoff s hs ∈
        arithmeticNonlocalTrace.domain ↔
      C3GenuineBracketGreenClosesAt s) ∧
    (C3GenuineBracketGreenClosesAt s ↔
      s.re = (1 : ℝ) / 2) := by
  exact
    ⟨genuineZero_scalarBracketChart_eq_zero hs hzero,
      primeMassGreenBulkState_mem_traceDomain_iff_c3GenuineBracketGreenClosesAt
        traceCutoff htraceCutoff hs,
      c3GenuineBracketGreenClosesAt_iff_re_eq_half hs⟩

/-- Global activation predicate for the differentiated Genuine bracket. -/
def GenuineZerosCloseC3GenuineBracketGreenForm : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    genuineContinuation s = 0 →
      C3GenuineBracketGreenClosesAt s

/-- Globally activating Green-bracket closure at every Genuine zero is exactly
the existing strong-nonvanishing frontier. -/
theorem genuineZerosCloseC3GenuineBracketGreenForm_iff_strongNonvanishing :
    GenuineZerosCloseC3GenuineBracketGreenForm ↔
      GenuineStrongNonvanishingInStrip := by
  simpa [GenuineZerosCloseC3GenuineBracketGreenForm,
    C3GenuineBracketGreenClosesAt] using
    genuineZeros_closeC3GenuineBracketGreenForm_iff_strongNonvanishing

/-- The zero-to-domain and zero-to-Green-closure formulations are globally
equivalent. This is the kernel-reflecting intertwiner stated as a relation,
without assuming that either side holds. -/
theorem genuineZerosLieInTraceDomain_iff_closeC3GenuineBracketGreenForm :
    GenuineZerosLieInArithmeticNonlocalTraceDomain ↔
      GenuineZerosCloseC3GenuineBracketGreenForm := by
  rw [genuineZero_to_arithmeticNonlocalTrace_domain_iff_strongNonvanishing,
    genuineZerosCloseC3GenuineBracketGreenForm_iff_strongNonvanishing]

/-- Global relational capstone. The operator-domain law, Green-bracket closure,
and strong confinement statement are exactly equivalent presentations of one
activation property. The theorem proves the equivalences; it does not declare
the activation property unconditionally. -/
theorem genuineBracket_global_relational_capstone :
    (GenuineZerosLieInArithmeticNonlocalTraceDomain ↔
      GenuineZerosCloseC3GenuineBracketGreenForm) ∧
    (GenuineZerosCloseC3GenuineBracketGreenForm ↔
      GenuineStrongNonvanishingInStrip) := by
  exact
    ⟨genuineZerosLieInTraceDomain_iff_closeC3GenuineBracketGreenForm,
      genuineZerosCloseC3GenuineBracketGreenForm_iff_strongNonvanishing⟩

end

end NativeCarryC3Crosswalk
