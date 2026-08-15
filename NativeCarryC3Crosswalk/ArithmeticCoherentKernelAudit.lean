import NativeCarryC3Crosswalk.ArithmeticNonlocalTrace
import NativeCarryC3Crosswalk.EnrichedTfvdPairTransport

/-!
# Linear arithmetic-carrier kernel audit

This module records two finite, parameter-free obstructions to using a
universal linear carrier as the missing Genuine-to-Green bridge.

First, the smallest already constructed joint carrier retaining both the
coarse two-scalar readout and the complete Green provenance has a nonzero
bulk direction in the kernel of the coarse readout.

Second, the same phenomenon occurs inside the universal enriched TFVD pair
transport itself.  There is a legitimate enriched input with exterior seed
`1`, zero value readout, and nonzero transported Green port, for every complex
parameter.

These are obstructions only to a **universal linear** kernel inclusion.  The
witness in the second theorem is not the canonical Dirichlet value/log-jet
pair.  Consequently this file makes no negative assertion about the
canonical arithmetic curve.  A successful smaller carrier would have to
encode the additional global condition that all blocks and the log jet arise
from one common Dirichlet parameter, rather than assume the desired kernel
inclusion as a field.

No zero hypothesis, critical-line equation, isotropic-membership assumption,
or confinement statement is used below.
-/

open scoped BigOperators ComplexConjugate

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp

noncomputable section

/-! ## Obstruction on the minimal joint linear carrier -/

/-- The existing finite joint relation is the smallest constructed linear
carrier retaining both the coarse readout and the complete Green leg. -/
abbrev FiniteC3ArithmeticJointCarrier :=
  finiteC3EnrichedJointRelation 2

/-- Coarse Genuine leg restricted to the joint carrier. -/
def finiteC3ArithmeticStateReadout :
    FiniteC3ArithmeticJointCarrier →ₗ[ℂ] (ℂ × ℂ) :=
  (LinearMap.fst ℂ (ℂ × ℂ) (FiniteC3GreenPortCarrier 2)).comp
    FiniteC3ArithmeticJointCarrier.subtype

/-- Complete Green/provenance leg restricted to the same carrier. -/
def finiteC3ArithmeticBulk :
    FiniteC3ArithmeticJointCarrier →ₗ[ℂ]
      FiniteC3GreenPortCarrier 2 :=
  (LinearMap.snd ℂ (ℂ × ℂ) (FiniteC3GreenPortCarrier 2)).comp
    FiniteC3ArithmeticJointCarrier.subtype

private def coarseKernelJointClass :
    FiniteC3MinimalProvenanceCarrier 2 :=
  minimalProvenanceQuotientMap
    (finiteC3CoarseBoundaryReadout 2)
    (finiteC3FullBoundaryAnalysis 2)
    finiteC3CoarseKernelWitness

private theorem finiteC3CoarseKernelWitness_ne_zero :
    finiteC3CoarseKernelWitness ≠ 0 := by
  intro hzero
  apply finiteC3CoarseKernelWitness_not_mem_diagonal
  rw [hzero]
  exact Submodule.zero_mem _

/-- The coarse-kernel witness internalized in the joint carrier. -/
private def finiteC3ArithmeticJointKernelWitness :
    FiniteC3ArithmeticJointCarrier := by
  refine ⟨(0, finiteC3CoarseKernelWitness), ?_⟩
  refine ⟨coarseKernelJointClass, ?_⟩
  apply Prod.ext
  · exact finiteC3CoarseBoundaryReadout_kernelWitness
  · rfl

@[simp] private theorem finiteC3ArithmeticStateReadout_kernelWitness :
    finiteC3ArithmeticStateReadout
      finiteC3ArithmeticJointKernelWitness = 0 := by
  rfl

private theorem finiteC3ArithmeticBulk_kernelWitness_ne_zero :
    finiteC3ArithmeticBulk
      finiteC3ArithmeticJointKernelWitness ≠ 0 := by
  simpa [finiteC3ArithmeticBulk,
    finiteC3ArithmeticJointKernelWitness] using
    finiteC3CoarseKernelWitness_ne_zero

/-- Exact failure of `ker stateReadout ≤ ker bulk` on the universal joint
linear carrier.  This theorem does not concern the smaller nonlinear locus of
canonical Dirichlet states. -/
theorem finiteC3Arithmetic_readoutKernel_not_le_bulkKernel :
    ¬ LinearMap.ker finiteC3ArithmeticStateReadout ≤
        LinearMap.ker finiteC3ArithmeticBulk := by
  intro hle
  have hreadout : finiteC3ArithmeticJointKernelWitness ∈
      LinearMap.ker finiteC3ArithmeticStateReadout := by
    exact LinearMap.mem_ker.mpr
      finiteC3ArithmeticStateReadout_kernelWitness
  have hbulk := LinearMap.mem_ker.mp (hle hreadout)
  exact finiteC3ArithmeticBulk_kernelWitness_ne_zero hbulk

/-! ## Obstruction inside the universal enriched TFVD transport -/

/-- A legitimate seeded TFVD port whose single complete block is
`(-1, 1, 0)`.  Its seed is the same exterior seed `1` used by the canonical
Genuine port, but its block is deliberately not claimed to be the canonical
Dirichlet block at any parameter. -/
private def seededZeroEnrichedTfvdPort : SeededEnrichedTfvdPort where
  seed := 1
  blocks := fun m =>
    enrichedAngularTfvdEncode m tfvdHaarScale 1 (-1) 1 0

private def zeroEnrichedTfvdPort : SeededEnrichedTfvdPort where
  seed := 0
  blocks := fun m =>
    enrichedAngularTfvdEncode m tfvdHaarScale 1 0 0 0

private def seededZeroEnrichedTfvdPair : EnrichedTfvdValueLogJetPair where
  value := seededZeroEnrichedTfvdPort
  logJet := zeroEnrichedTfvdPort

private theorem seededZeroEnrichedTfvdPort_valueReadout :
    finiteSeededEnrichedTfvdGenuineReadout
      1 tfvdHaarScale (fun _ => 1) seededZeroEnrichedTfvdPort = 0 := by
  unfold finiteSeededEnrichedTfvdGenuineReadout
    finiteEnrichedTfvdGenuineBracketReadout
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp only [seededZeroEnrichedTfvdPort]
  rw [enrichedTfvdGenuineBracketReadout_encode
    0 tfvdHaarScale_ne_zero (by norm_num)]
  norm_num

private theorem seededZeroTransportedGreenPort_ne_zero (s : ℂ) :
    finiteC3EnrichedTfvdValueGreenPort
        1 tfvdHaarScale (fun _ => 1) s seededZeroEnrichedTfvdPort ≠ 0 := by
  intro hzero
  have hcoord := congrArg
    (fun z : FiniteC3GreenPortCarrier 3 => z.2 0) hzero
  change
    (finiteC3EnrichedTfvdValueGreenPort
      1 tfvdHaarScale (fun _ => 1) s seededZeroEnrichedTfvdPort).2
        (finProdFinEquiv (0, 0)) = 0 at hcoord
  rw [finiteC3EnrichedTfvdValueGreenPort_snd_finProd] at hcoord
  simp only [seededZeroEnrichedTfvdPort, Fin.val_zero] at hcoord
  rw [enrichedAngularTfvdCoordinateToCpGreenTriple_encode
    3 0 tfvdHaarScale_ne_zero (by norm_num)] at hcoord
  simp only [cpGreenTfvdTripleEdge_zero,
    cpGreenTfvdCoordinateFromHorizontal] at hcoord
  rw [tfvdDecode_encode 0 tfvdHaarScale_ne_zero (by norm_num)] at hcoord
  norm_num at hcoord

/-- For every complex parameter, the universal enriched TFVD pair transport
admits a typed input with seed `1`, zero Genuine value readout, and nonzero
complete Green port.  The result is universal in the parameter precisely
because it audits the full linear transport domain, not the canonical
Dirichlet curve. -/
theorem exists_enrichedTfvdPairTransport_valueKernel_greenPort_nonzero
    (s : ℂ) :
    ∃ pair : EnrichedTfvdValueLogJetPair,
      let data := finiteC3EnrichedTfvdPairTransport
        1 tfvdHaarScale (fun _ => 1) s pair
      data.valueReadout = 0 ∧ data.greenPort ≠ 0 := by
  refine ⟨seededZeroEnrichedTfvdPair, ?_⟩
  dsimp [finiteC3EnrichedTfvdPairTransport,
    seededZeroEnrichedTfvdPair]
  exact ⟨seededZeroEnrichedTfvdPort_valueReadout,
    seededZeroTransportedGreenPort_ne_zero s⟩

end

end NativeCarryC3Crosswalk
