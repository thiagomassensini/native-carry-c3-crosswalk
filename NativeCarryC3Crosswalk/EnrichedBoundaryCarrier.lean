import NativeCarryC3Crosswalk.ReflectedGreenBoundaryForm
import CPFormal.Analytic.CpMinimalProvenanceQuotient
import CPFormal.Analytic.CpGenuineGreenKernelInclusion
import CPFormal.Analytic.CpReflectedGreenBridge

/-!
# Minimal-provenance carrier for the finite C3 Green port

Scalar synthesis forgets the arithmetic cell at which a boundary value was
produced.  The reflected Green form, by contrast, pairs equal cells before
synthesis.  This file applies the canonical minimal-provenance quotient from
`CPFormal` to that exact finite C3 situation.

The coarse leg sums each of the two boundary vectors.  The analysis leg keeps
the complete pair.  Consequently their joint kernel is trivial: the coarsest
carrier retaining both readouts is canonically the full finite port.  Its
joint-range realization is a closed finite-dimensional relation, so no
section, pseudoinverse, or preferred representative is introduced.

The final section audits the hoped-for isotropic membership.  For the fixed
diagonal Green relation it is equivalent, in the Genuine strip, to
`Re(s) = 1 / 2`.  Uniformly over Genuine zeros it is equivalent to the already
named strong nonvanishing frontier.  Thus the enriched carrier is constructed
and closed here, while the zero-to-membership law is neither hidden in its
definition nor obtained from scalar synthesis alone.
-/

open scoped BigOperators ComplexConjugate

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary

noncomputable section

/-- The full two-leg C3 port before scalar synthesis. -/
abbrev FiniteC3GreenPortCarrier (M : ℕ) :=
  FiniteC3GreenBoundarySpace M × FiniteC3GreenBoundarySpace M

/-- Sum all preserved cells of one finite boundary vector. -/
def finiteC3VectorSynthesis (M : ℕ) :
    FiniteC3GreenBoundarySpace M →ₗ[ℂ] ℂ where
  toFun x := ∑ n : Fin M, x n
  map_add' x y := by
    change ∑ n : Fin M, (x.ofLp n + y.ofLp n) =
      (∑ n : Fin M, x.ofLp n) + ∑ n : Fin M, y.ofLp n
    exact Finset.sum_add_distrib
  map_smul' c x := by
    change ∑ n : Fin M, c * x.ofLp n = c * ∑ n : Fin M, x.ofLp n
    rw [Finset.mul_sum]

@[simp] theorem finiteC3VectorSynthesis_apply
    (M : ℕ) (x : FiniteC3GreenBoundarySpace M) :
    finiteC3VectorSynthesis M x = ∑ n : Fin M, x n :=
  rfl

/-- Coarse two-scalar readout obtained only after all cell labels are erased. -/
def finiteC3CoarseBoundaryReadout (M : ℕ) :
    FiniteC3GreenPortCarrier M →ₗ[ℂ] (ℂ × ℂ) where
  toFun x :=
    (finiteC3VectorSynthesis M x.1, finiteC3VectorSynthesis M x.2)
  map_add' x y := by
    apply Prod.ext
    · exact (finiteC3VectorSynthesis M).map_add x.1 y.1
    · exact (finiteC3VectorSynthesis M).map_add x.2 y.2
  map_smul' c x := by
    apply Prod.ext
    · exact (finiteC3VectorSynthesis M).map_smul c x.1
    · exact (finiteC3VectorSynthesis M).map_smul c x.2

@[simp] theorem finiteC3CoarseBoundaryReadout_apply
    (M : ℕ) (x : FiniteC3GreenPortCarrier M) :
    finiteC3CoarseBoundaryReadout M x =
      (finiteC3VectorSynthesis M x.1,
        finiteC3VectorSynthesis M x.2) :=
  rfl

/-- Provenance-preserving analysis leg: every cell and both Green coordinates
remain present. -/
def finiteC3FullBoundaryAnalysis (M : ℕ) :
    FiniteC3GreenPortCarrier M →ₗ[ℂ] FiniteC3GreenPortCarrier M :=
  LinearMap.id

@[simp] theorem finiteC3FullBoundaryAnalysis_apply
    (M : ℕ) (x : FiniteC3GreenPortCarrier M) :
    finiteC3FullBoundaryAnalysis M x = x :=
  rfl

/-- The coarsest quotient retaining both the scalar synthesis and the full
Green analysis. -/
abbrev FiniteC3MinimalProvenanceCarrier (M : ℕ) :=
  MinimalProvenanceCarrier
    (finiteC3CoarseBoundaryReadout M)
    (finiteC3FullBoundaryAnalysis M)

/-- No nonzero direction may be removed while the complete Green port is
retained. -/
theorem finiteC3_minimalProvenanceKernel_eq_bot (M : ℕ) :
    minimalProvenanceKernel
        (finiteC3CoarseBoundaryReadout M)
        (finiteC3FullBoundaryAnalysis M) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hzero : finiteC3FullBoundaryAnalysis M x = 0 :=
    LinearMap.mem_ker.mp hx.2
  simpa using hzero

/-- The minimal-provenance quotient is canonically the uncompressed finite
port.  This is a theorem, not a choice of representative. -/
def finiteC3MinimalProvenanceEquivPort (M : ℕ) :
    FiniteC3MinimalProvenanceCarrier M ≃ₗ[ℂ]
      FiniteC3GreenPortCarrier M :=
  (minimalProvenanceKernel
      (finiteC3CoarseBoundaryReadout M)
      (finiteC3FullBoundaryAnalysis M)).quotEquivOfEqBot
    (finiteC3_minimalProvenanceKernel_eq_bot M)

/-- Canonical enriched class of the arithmetic C3 Green pair. -/
def finiteC3EnrichedBoundaryState (M : ℕ) (s : ℂ) :
    FiniteC3MinimalProvenanceCarrier M :=
  minimalProvenanceQuotientMap
    (finiteC3CoarseBoundaryReadout M)
    (finiteC3FullBoundaryAnalysis M)
    (finiteC3GreenBoundaryPair M s)

/-- Under the canonical equivalence (available because the joint kernel is
trivial), the enriched arithmetic class is literally its complete C3 port. -/
@[simp] theorem finiteC3MinimalProvenanceEquivPort_state
    (M : ℕ) (s : ℂ) :
    finiteC3MinimalProvenanceEquivPort M
        (finiteC3EnrichedBoundaryState M s) =
      finiteC3GreenBoundaryPair M s := by
  apply Submodule.quotEquivOfEqBot_apply_mk

/-- The analysis leg of the enriched class recovers the whole C3 port. -/
@[simp] theorem finiteC3EnrichedBoundaryState_analysis
    (M : ℕ) (s : ℂ) :
    minimalProvenanceA
        (finiteC3CoarseBoundaryReadout M)
        (finiteC3FullBoundaryAnalysis M)
        (finiteC3EnrichedBoundaryState M s) =
      finiteC3GreenBoundaryPair M s := by
  rfl

/-- The coarse leg of the same class is exactly scalar synthesis of its two
port coordinates. -/
@[simp] theorem finiteC3EnrichedBoundaryState_coarse
    (M : ℕ) (s : ℂ) :
    minimalProvenanceQ
        (finiteC3CoarseBoundaryReadout M)
        (finiteC3FullBoundaryAnalysis M)
        (finiteC3EnrichedBoundaryState M s) =
      finiteC3CoarseBoundaryReadout M
        (finiteC3GreenBoundaryPair M s) := by
  rfl

/-- Descended joint readout on the minimal-provenance carrier. -/
def finiteC3EnrichedJointMap (M : ℕ) :
    FiniteC3MinimalProvenanceCarrier M →ₗ[ℂ]
      ((ℂ × ℂ) × FiniteC3GreenPortCarrier M) :=
  (minimalProvenanceQ
      (finiteC3CoarseBoundaryReadout M)
      (finiteC3FullBoundaryAnalysis M)).prod
    (minimalProvenanceA
      (finiteC3CoarseBoundaryReadout M)
      (finiteC3FullBoundaryAnalysis M))

@[simp] theorem finiteC3EnrichedJointMap_apply
    (M : ℕ) (x : FiniteC3MinimalProvenanceCarrier M) :
    finiteC3EnrichedJointMap M x =
      (minimalProvenanceQ
          (finiteC3CoarseBoundaryReadout M)
          (finiteC3FullBoundaryAnalysis M) x,
        minimalProvenanceA
          (finiteC3CoarseBoundaryReadout M)
          (finiteC3FullBoundaryAnalysis M) x) :=
  rfl

/-- Joint scalar/provenance relation realized by the enriched carrier. -/
def finiteC3EnrichedJointRelation (M : ℕ) :
    Submodule ℂ ((ℂ × ℂ) × FiniteC3GreenPortCarrier M) :=
  LinearMap.range (finiteC3EnrichedJointMap M)

/-- The canonical arithmetic state realizes its paired coarse/provenance
readout inside the joint relation, without choosing a lift. -/
theorem finiteC3EnrichedBoundaryState_joint_mem
    (M : ℕ) (s : ℂ) :
    (finiteC3CoarseBoundaryReadout M (finiteC3GreenBoundaryPair M s),
        finiteC3GreenBoundaryPair M s) ∈
      finiteC3EnrichedJointRelation M := by
  refine ⟨finiteC3EnrichedBoundaryState M s, ?_⟩
  rfl

/-- The finite enriched relation is closed.  Finite dimensionality, rather
than a selected inverse of the coarse readout, supplies the topology. -/
theorem finiteC3EnrichedJointRelation_isClosed (M : ℕ) :
    IsClosed (finiteC3EnrichedJointRelation M :
      Set ((ℂ × ℂ) × FiniteC3GreenPortCarrier M)) :=
  Submodule.closed_of_finiteDimensional _

/-- The reflected CP Green form is unchanged after passing through the
minimal-provenance carrier and reading its analysis leg. -/
theorem greenForm_finiteC3EnrichedBoundaryState_eq_orientedFlux
    (M : ℕ) (s : ℂ) :
    greenForm
        (minimalProvenanceA
          (finiteC3CoarseBoundaryReadout M)
          (finiteC3FullBoundaryAnalysis M)
          (finiteC3EnrichedBoundaryState M s))
        (minimalProvenanceA
          (finiteC3CoarseBoundaryReadout M)
          (finiteC3FullBoundaryAnalysis M)
          (finiteC3EnrichedBoundaryState M (reflectedParameter s))) =
      finiteOrientedCpGreenFlux 3 M s := by
  simpa using greenForm_finiteC3GreenBoundaryPair_eq_orientedFlux M s

/-! ## Exact audit of isotropic membership -/

/-- Diagonal boundary relation, the graph of the identity port law. -/
def finiteC3DiagonalGreenRelation (M : ℕ) :
    GreenRelation ℂ (FiniteC3GreenBoundarySpace M) :=
  LinearMap.range
    ((LinearMap.id : FiniteC3GreenBoundarySpace M →ₗ[ℂ]
      FiniteC3GreenBoundarySpace M).prod LinearMap.id)

/-- Membership in the diagonal relation is equality of the two port legs. -/
theorem mem_finiteC3DiagonalGreenRelation_iff
    (M : ℕ) (x : FiniteC3GreenPortCarrier M) :
    x ∈ finiteC3DiagonalGreenRelation M ↔ x.1 = x.2 := by
  constructor
  · rintro ⟨u, rfl⟩
    rfl
  · intro h
    refine ⟨x.1, ?_⟩
    exact Prod.ext rfl h

/-- The diagonal relation is Green-isotropic independently of `s`. -/
theorem finiteC3DiagonalGreenRelation_isGreenIsotropic (M : ℕ) :
    IsGreenIsotropic (finiteC3DiagonalGreenRelation M) := by
  rw [isGreenIsotropic_iff_green_identity]
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  simp [greenForm]

/-- At the quadratic equilibrium, every finite direct C3 port belongs to the
fixed diagonal Green relation. -/
theorem finiteC3GreenBoundaryPair_mem_diagonal_of_re_eq_half
    (M : ℕ) {s : ℂ} (hre : s.re = (1 : ℝ) / 2) :
    finiteC3GreenBoundaryPair M s ∈
      finiteC3DiagonalGreenRelation M := by
  rw [mem_finiteC3DiagonalGreenRelation_iff]
  ext n
  rw [finiteC3GreenBoundaryPair_fst_apply,
    finiteC3GreenBoundaryPair_snd_apply,
    phaseNormalizedCpBlockGradient_eq_radial_mul 3 (by norm_num)]
  simp [criticalDisplacement, hre]

/-- The reflected port satisfies the same fixed relation at equilibrium. -/
theorem finiteC3ReflectedGreenBoundaryPair_mem_diagonal_of_re_eq_half
    (M : ℕ) {s : ℂ} (hre : s.re = (1 : ℝ) / 2) :
    finiteC3GreenBoundaryPair M (reflectedParameter s) ∈
      finiteC3DiagonalGreenRelation M := by
  apply finiteC3GreenBoundaryPair_mem_diagonal_of_re_eq_half
  norm_num [hre]

/-- Concrete all-cutoff membership statement for the enriched direct and
reflected ports. -/
def C3EnrichedDiagonalBoundaryTransportAt (s : ℂ) : Prop :=
  ∀ M : ℕ,
    finiteC3GreenBoundaryPair M s ∈ finiteC3DiagonalGreenRelation M ∧
      finiteC3GreenBoundaryPair M (reflectedParameter s) ∈
        finiteC3DiagonalGreenRelation M

/-- In the Genuine strip, the concrete diagonal membership is exactly the
critical half-abscissa.  The forward direction uses the nonempty cutoff
`M = 1`, so no empty-carrier shortcut is possible. -/
theorem c3EnrichedDiagonalBoundaryTransportAt_iff_re_eq_half
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    C3EnrichedDiagonalBoundaryTransportAt s ↔
      s.re = (1 : ℝ) / 2 := by
  constructor
  · intro htransport
    have hports := htransport 1
    have hflux :=
      finiteOrientedC3GreenFlux_eq_zero_of_isotropicBoundary
        1 s (finiteC3DiagonalGreenRelation 1)
        (finiteC3DiagonalGreenRelation_isGreenIsotropic 1)
        hports.1 hports.2
    have hphase : finitePhaseNormalizedCpGreenFlux 3 1 s = 0 := by
      simpa [finiteOrientedCpGreenFlux] using congrArg Neg.neg hflux
    exact
      (finitePhaseNormalizedCpGreenFlux_eq_zero_iff_re_eq_half
        3 1 (by norm_num) (by norm_num) hs).1 hphase
  · intro hre M
    exact
      ⟨finiteC3GreenBoundaryPair_mem_diagonal_of_re_eq_half M hre,
        finiteC3ReflectedGreenBoundaryPair_mem_diagonal_of_re_eq_half M hre⟩

/-- Asking every Genuine zero to land in this fixed enriched diagonal carrier
is exactly the already isolated strong nonvanishing frontier.  The carrier
therefore removes the type/provenance obstruction without silently assuming
the remaining arithmetic zero-to-port law. -/
theorem genuineZerosLandInC3EnrichedDiagonalCarrier_iff_strongNonvanishing :
    (∀ {s : ℂ}, s ∈ genuineCriticalStrip →
        genuineContinuation s = 0 →
        C3EnrichedDiagonalBoundaryTransportAt s) ↔
      GenuineStrongNonvanishingInStrip := by
  constructor
  · intro hcarrier s hs hoff hzero
    have hre :=
      (c3EnrichedDiagonalBoundaryTransportAt_iff_re_eq_half hs).1
        (hcarrier hs hzero)
    exact hoff hre
  · intro hstrong s hs hzero
    apply (c3EnrichedDiagonalBoundaryTransportAt_iff_re_eq_half hs).2
    by_contra hoff
    exact (hstrong hs hoff) hzero

end

end NativeCarryC3Crosswalk
