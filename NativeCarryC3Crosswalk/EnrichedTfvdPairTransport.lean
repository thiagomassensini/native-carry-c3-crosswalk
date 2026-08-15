import NativeCarryC3Crosswalk.GenuineBracketGreenIdentity
import CPFormal.Analytic.CpFiniteGenuineTfvdProvenanceGluing

/-!
# Enriched value--log-jet transport to the finite C3 Green port

The scalar Genuine chart and the reflected Green form have different arity:
the former is a linear readout, while the latter pairs two boundary states.
Consequently the relevant transport cannot act on the synthesized scalar
alone.  This module constructs the finite transport on the enriched pair
that exists before scalar synthesis.

The input retains

* the seeded value port;
* the seeded log-jet port;
* all three residues of every angular block.

The output retains both scalar readouts, the returned same-parameter boundary
cells, and the complete C3 Green port.  On the canonical arithmetic pair the
transport recovers literally the finite Genuine chart, its log-jet chart, and
the bracket-resolved Green boundary pair.  The existing provenance identity
then becomes an equality on the transported pair, for every complex
parameter and without a zero or critical-line hypothesis.
-/

open scoped BigOperators ComplexConjugate

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary

noncomputable section

/-- The two enriched TFVD legs required before a bilinear boundary form can
be evaluated.  Keeping only `value` would preserve the scalar chart but lose
the log-jet leg needed by the same-parameter boundary pairing. -/
structure EnrichedTfvdValueLogJetPair where
  value : SeededEnrichedTfvdPort
  logJet : SeededEnrichedTfvdPort

/-- Canonical arithmetic value/log-jet pair at the parameter `s`. -/
def canonicalEnrichedTfvdValueLogJetPair
    (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) :
    EnrichedTfvdValueLogJetPair :=
  {
    value := canonicalSeededEnrichedTfvdGenuinePort kappa omega s
    logJet := canonicalSeededEnrichedTfvdLogJetPort kappa omega s
  }

/-- Select one of the three provenance-preserving Green coordinates of an
angular block. -/
def cpGreenTfvdTripleEdge
    (z : CpGreenTfvdTriple) : Fin 3 → TfvdCoordinate :=
  Fin.cases z.first (Fin.cases z.second (fun _ ↦ z.dormant))

@[simp] theorem cpGreenTfvdTripleEdge_zero (z : CpGreenTfvdTriple) :
    cpGreenTfvdTripleEdge z 0 = z.first :=
  rfl

@[simp] theorem cpGreenTfvdTripleEdge_one (z : CpGreenTfvdTriple) :
    cpGreenTfvdTripleEdge z 1 = z.second :=
  rfl

@[simp] theorem cpGreenTfvdTripleEdge_two (z : CpGreenTfvdTriple) :
    cpGreenTfvdTripleEdge z 2 = z.dormant :=
  rfl

/-- Decoding a canonical Green coordinate recovers its two actual boundary
legs. -/
theorem tfvdDecode_canonicalCpGreenTfvdCoordinate
    (p n : ℕ) (s : ℂ) :
    tfvdDecode tfvdHaarScale 1
        (canonicalCpGreenTfvdCoordinate p n s) =
      (phaseNormalizedCpBlockGradient p s n,
        positiveDirichletGradient s n) := by
  unfold canonicalCpGreenTfvdCoordinate
  exact tfvdDecode_encode n tfvdHaarScale_ne_zero (by norm_num)
    (phaseNormalizedCpBlockGradient p s n)
    (positiveDirichletGradient s n)

/-- Global finite C3 Green port obtained by returning every enriched value
block and flattening its three residues.  The block/residue equivalence is
canonical; no representative, inverse, or scalar reconstruction is chosen. -/
def finiteC3EnrichedTfvdValueGreenPort
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ)
    (port : SeededEnrichedTfvdPort) :
    FiniteC3GreenPortCarrier (M * 3) :=
  let coordinate := fun n : Fin (M * 3) ↦
    let mr := finProdFinEquiv.symm n
    cpGreenTfvdTripleEdge
      (enrichedAngularTfvdCoordinateToCpGreenTriple
        3 kappa (omega mr.1) s (port.blocks mr.1)) mr.2
  (WithLp.toLp 2 (fun n ↦
      (tfvdDecode tfvdHaarScale 1 (coordinate n)).1),
    WithLp.toLp 2 (fun n ↦
      (tfvdDecode tfvdHaarScale 1 (coordinate n)).2))

@[simp] theorem finiteC3EnrichedTfvdValueGreenPort_fst_finProd
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ)
    (port : SeededEnrichedTfvdPort) (m : Fin M) (r : Fin 3) :
    (finiteC3EnrichedTfvdValueGreenPort M kappa omega s port).1
        (finProdFinEquiv (m, r)) =
      (tfvdDecode tfvdHaarScale 1
        (cpGreenTfvdTripleEdge
          (enrichedAngularTfvdCoordinateToCpGreenTriple
            3 kappa (omega m) s (port.blocks m)) r)).1 := by
  unfold finiteC3EnrichedTfvdValueGreenPort
  dsimp only
  rw [Equiv.symm_apply_apply]

@[simp] theorem finiteC3EnrichedTfvdValueGreenPort_snd_finProd
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ)
    (port : SeededEnrichedTfvdPort) (m : Fin M) (r : Fin 3) :
    (finiteC3EnrichedTfvdValueGreenPort M kappa omega s port).2
        (finProdFinEquiv (m, r)) =
      (tfvdDecode tfvdHaarScale 1
        (cpGreenTfvdTripleEdge
          (enrichedAngularTfvdCoordinateToCpGreenTriple
            3 kappa (omega m) s (port.blocks m)) r)).2 := by
  unfold finiteC3EnrichedTfvdValueGreenPort
  dsimp only
  rw [Equiv.symm_apply_apply]

/-- Complete finite output of the enriched pair transport.  The scalar
readouts are recorded alongside, rather than instead of, the local boundary
cells and the full Green port. -/
structure FiniteC3EnrichedTfvdPairTransportData (M : ℕ) where
  valueReadout : ℂ
  logJetReadout : ℂ
  boundaryCells : Fin M → TfvdSameSBoundaryCells
  greenPort : FiniteC3GreenPortCarrier (M * 3)

/-- The desired finite `J_M`: it acts on the enriched value/log-jet pair
before synthesis and preserves every component used by either readout. -/
def finiteC3EnrichedTfvdPairTransport
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ)
    (pair : EnrichedTfvdValueLogJetPair) :
    FiniteC3EnrichedTfvdPairTransportData M :=
  {
    valueReadout :=
      finiteSeededEnrichedTfvdGenuineReadout M kappa omega pair.value
    logJetReadout :=
      finiteSeededEnrichedTfvdGenuineReadout M kappa omega pair.logJet
    boundaryCells := fun m ↦
      enrichedTfvdSameSBoundaryCells kappa (omega m)
        (pair.value.blocks m) (pair.logJet.blocks m)
    greenPort :=
      finiteC3EnrichedTfvdValueGreenPort M kappa omega s pair.value
  }

/-- Boundary form of an arbitrary enriched pair, formed cellwise before the
finite sum. -/
def finiteC3EnrichedTfvdPairBoundaryForm
    (M : ℕ) (data : FiniteC3EnrichedTfvdPairTransportData M) : ℂ :=
  ∑ m : Fin M, (data.boundaryCells m).total

/-!
## Universal pair-level Green ledger
-/

/-- One cell of the abstract Green form, kept before summation. -/
def finiteC3GreenPortEdge
    {N : ℕ} (direct reflected : FiniteC3GreenPortCarrier N)
    (n : Fin N) : ℂ :=
  (starRingEnd ℂ) (direct.2 n) * reflected.1 n -
    (starRingEnd ℂ) (direct.1 n) * reflected.2 n

/-- The abstract finite Green form is the sum of its provenance-labelled
cells. -/
theorem greenForm_eq_sum_finiteC3GreenPortEdge
    {N : ℕ} (direct reflected : FiniteC3GreenPortCarrier N) :
    greenForm direct reflected =
      ∑ n : Fin N, finiteC3GreenPortEdge direct reflected n := by
  rw [greenForm, PiLp.inner_apply, PiLp.inner_apply,
    ← Finset.sum_sub_distrib]
  simp only [finiteC3GreenPortEdge, RCLike.inner_apply']

/-- Four explicit leg transports taking an arbitrary same-parameter TFVD
cell to an arbitrary direct/reflected Green cell.  This is not defined as the
difference between two global totals. -/
def tfvdPairGreenLegChannels
    (left right jetLeft jetRight : ℂ)
    (directRadial directHorizontal reflectedRadial
      reflectedHorizontal : ℂ) :
    TfvdSameSGreenLegChannels :=
  {
    rightValueTransport :=
      (right - (starRingEnd ℂ) directHorizontal) * jetLeft
    jetLeftTransport :=
      (starRingEnd ℂ) directHorizontal *
        (jetLeft - reflectedRadial)
    leftValueTransport :=
      -(left - (starRingEnd ℂ) directRadial) * jetRight
    jetRightTransport :=
      -(starRingEnd ℂ) directRadial *
        (jetRight - reflectedHorizontal)
  }

/-- Universal one-cell transport identity.  It is a polynomial identity in
eight arbitrary complex coordinates; no arithmetic state, zero, reflection
law, or critical-line equation is used. -/
theorem sameSEdgeBoundaryWedge_eq_greenEdge_add_pairChannels
    (left right jetLeft jetRight : ℂ)
    (directRadial directHorizontal reflectedRadial
      reflectedHorizontal : ℂ) :
    sameSEdgeBoundaryWedge left right jetLeft jetRight =
      ((starRingEnd ℂ) directHorizontal * reflectedRadial -
        (starRingEnd ℂ) directRadial * reflectedHorizontal) +
      (tfvdPairGreenLegChannels left right jetLeft jetRight
        directRadial directHorizontal reflectedRadial
          reflectedHorizontal).total := by
  unfold sameSEdgeBoundaryWedge tfvdPairGreenLegChannels
    TfvdSameSGreenLegChannels.total
  ring

/-- Explicit provenance ledger of one three-residue block.  The two visible
cells use their four leg transports; the third Green cell is retained as a
dormant compensation instead of being discarded. -/
def finiteC3EnrichedTfvdBlockGreenProvenance
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (pair : EnrichedTfvdValueLogJetPair)
    (direct reflected : FiniteC3EnrichedTfvdPairTransportData M)
    (m : Fin M) : TfvdSameSGreenProvenanceChannels :=
  let valueEdges :=
    enrichedAngularTfvdDecode kappa (omega m) (pair.value.blocks m)
  let jetEdges :=
    enrichedAngularTfvdDecode kappa (omega m) (pair.logJet.blocks m)
  let i0 : Fin (M * 3) := finProdFinEquiv (m, 0)
  let i1 : Fin (M * 3) := finProdFinEquiv (m, 1)
  let i2 : Fin (M * 3) := finProdFinEquiv (m, 2)
  {
    visibleLegs :=
      tfvdPairGreenLegChannels
        valueEdges.first valueEdges.second
        jetEdges.first jetEdges.second
        (direct.greenPort.1 i0) (direct.greenPort.2 i0)
        (reflected.greenPort.1 i0) (reflected.greenPort.2 i0)
    dormantLegs :=
      tfvdPairGreenLegChannels
        valueEdges.second valueEdges.dormant
        jetEdges.second jetEdges.dormant
        (direct.greenPort.1 i1) (direct.greenPort.2 i1)
        (reflected.greenPort.1 i1) (reflected.greenPort.2 i1)
    dormantGreenCompensation :=
      -finiteC3GreenPortEdge direct.greenPort reflected.greenPort i2
  }

/-- Global provenance is summed only after every block and every leg has
been retained. -/
def finiteC3EnrichedTfvdPairGreenProvenance
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (pair : EnrichedTfvdValueLogJetPair)
    (direct reflected : FiniteC3EnrichedTfvdPairTransportData M) : ℂ :=
  ∑ m : Fin M,
    (finiteC3EnrichedTfvdBlockGreenProvenance
      M kappa omega pair direct reflected m).total

/-- Blockwise form of the universal ledger. -/
theorem finiteC3EnrichedTfvdPair_blockBoundary_eq_greenEdges_add_provenance
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ)
    (pair reflectedPair : EnrichedTfvdValueLogJetPair) (m : Fin M) :
    let direct :=
      finiteC3EnrichedTfvdPairTransport M kappa omega s pair
    let reflected :=
      finiteC3EnrichedTfvdPairTransport M kappa omega
        (reflectedParameter s) reflectedPair
    (direct.boundaryCells m).total =
      (finiteC3GreenPortEdge direct.greenPort reflected.greenPort
          (finProdFinEquiv (m, 0)) +
        finiteC3GreenPortEdge direct.greenPort reflected.greenPort
          (finProdFinEquiv (m, 1)) +
        finiteC3GreenPortEdge direct.greenPort reflected.greenPort
          (finProdFinEquiv (m, 2))) +
      (finiteC3EnrichedTfvdBlockGreenProvenance
        M kappa omega pair direct reflected m).total := by
  dsimp only [finiteC3EnrichedTfvdPairTransport]
  unfold enrichedTfvdSameSBoundaryCells TfvdSameSBoundaryCells.total
    finiteC3EnrichedTfvdBlockGreenProvenance
    TfvdSameSGreenProvenanceChannels.total
    sameSEdgeBoundaryWedge tfvdPairGreenLegChannels
    TfvdSameSGreenLegChannels.total finiteC3GreenPortEdge
  dsimp only
  ring

/-- Reindex the `M * 3` Green cells as `M` labelled blocks with three
residues each. -/
theorem sum_finiteC3GreenPortEdge_eq_sum_blocks
    (M : ℕ)
    (direct reflected : FiniteC3GreenPortCarrier (M * 3)) :
    (∑ n : Fin (M * 3), finiteC3GreenPortEdge direct reflected n) =
      ∑ m : Fin M,
        (finiteC3GreenPortEdge direct reflected (finProdFinEquiv (m, 0)) +
          finiteC3GreenPortEdge direct reflected (finProdFinEquiv (m, 1)) +
          finiteC3GreenPortEdge direct reflected
            (finProdFinEquiv (m, 2))) := by
  calc
    (∑ n : Fin (M * 3), finiteC3GreenPortEdge direct reflected n) =
        ∑ mr : Fin M × Fin 3,
          finiteC3GreenPortEdge direct reflected (finProdFinEquiv mr) := by
      exact (Equiv.sum_comp finProdFinEquiv
        (finiteC3GreenPortEdge direct reflected)).symm
    _ = ∑ m : Fin M, ∑ r : Fin 3,
          finiteC3GreenPortEdge direct reflected
            (finProdFinEquiv (m, r)) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ m : Fin M,
        (finiteC3GreenPortEdge direct reflected (finProdFinEquiv (m, 0)) +
          finiteC3GreenPortEdge direct reflected (finProdFinEquiv (m, 1)) +
          finiteC3GreenPortEdge direct reflected
            (finProdFinEquiv (m, 2))) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Fin.sum_univ_three]

/-- Universal enriched-pair transport identity.  It holds for arbitrary
typed value/log-jet ports on both sides of the reflected pairing.  The
canonical arithmetic state is only a later specialization. -/
theorem finiteC3EnrichedTfvdPairBoundary_eq_greenForm_add_provenance
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ)
    (pair reflectedPair : EnrichedTfvdValueLogJetPair) :
    let direct :=
      finiteC3EnrichedTfvdPairTransport M kappa omega s pair
    let reflected :=
      finiteC3EnrichedTfvdPairTransport M kappa omega
        (reflectedParameter s) reflectedPair
    finiteC3EnrichedTfvdPairBoundaryForm M direct =
      greenForm direct.greenPort reflected.greenPort +
        finiteC3EnrichedTfvdPairGreenProvenance
          M kappa omega pair direct reflected := by
  dsimp only
  unfold finiteC3EnrichedTfvdPairBoundaryForm
    finiteC3EnrichedTfvdPairGreenProvenance
  rw [greenForm_eq_sum_finiteC3GreenPortEdge,
    sum_finiteC3GreenPortEdge_eq_sum_blocks]
  calc
    (∑ m : Fin M,
        ((finiteC3EnrichedTfvdPairTransport M kappa omega s pair).boundaryCells
          m).total) =
        ∑ m : Fin M,
          ((finiteC3GreenPortEdge
                (finiteC3EnrichedTfvdPairTransport
                  M kappa omega s pair).greenPort
                (finiteC3EnrichedTfvdPairTransport M kappa omega
                  (reflectedParameter s) reflectedPair).greenPort
                (finProdFinEquiv (m, 0)) +
              finiteC3GreenPortEdge
                (finiteC3EnrichedTfvdPairTransport
                  M kappa omega s pair).greenPort
                (finiteC3EnrichedTfvdPairTransport M kappa omega
                  (reflectedParameter s) reflectedPair).greenPort
                (finProdFinEquiv (m, 1)) +
              finiteC3GreenPortEdge
                (finiteC3EnrichedTfvdPairTransport
                  M kappa omega s pair).greenPort
                (finiteC3EnrichedTfvdPairTransport M kappa omega
                  (reflectedParameter s) reflectedPair).greenPort
                (finProdFinEquiv (m, 2))) +
            (finiteC3EnrichedTfvdBlockGreenProvenance
              M kappa omega pair
                (finiteC3EnrichedTfvdPairTransport
                  M kappa omega s pair)
                (finiteC3EnrichedTfvdPairTransport M kappa omega
                  (reflectedParameter s) reflectedPair) m).total) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact finiteC3EnrichedTfvdPair_blockBoundary_eq_greenEdges_add_provenance
        M kappa omega s pair reflectedPair m
    _ =
        (∑ m : Fin M,
          (finiteC3GreenPortEdge
                (finiteC3EnrichedTfvdPairTransport
                  M kappa omega s pair).greenPort
                (finiteC3EnrichedTfvdPairTransport M kappa omega
                  (reflectedParameter s) reflectedPair).greenPort
                (finProdFinEquiv (m, 0)) +
            finiteC3GreenPortEdge
                (finiteC3EnrichedTfvdPairTransport
                  M kappa omega s pair).greenPort
                (finiteC3EnrichedTfvdPairTransport M kappa omega
                  (reflectedParameter s) reflectedPair).greenPort
                (finProdFinEquiv (m, 1)) +
            finiteC3GreenPortEdge
                (finiteC3EnrichedTfvdPairTransport
                  M kappa omega s pair).greenPort
                (finiteC3EnrichedTfvdPairTransport M kappa omega
                  (reflectedParameter s) reflectedPair).greenPort
                (finProdFinEquiv (m, 2)))) +
          ∑ m : Fin M,
            (finiteC3EnrichedTfvdBlockGreenProvenance
              M kappa omega pair
                (finiteC3EnrichedTfvdPairTransport
                  M kappa omega s pair)
                (finiteC3EnrichedTfvdPairTransport M kappa omega
                  (reflectedParameter s) reflectedPair) m).total := by
      rw [Finset.sum_add_distrib]

/-- The canonical enriched value leg is transported to the complete C3
Genuine/Green port, not merely to its synthesized scalar. -/
theorem finiteC3EnrichedTfvdValueGreenPort_canonical
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    finiteC3EnrichedTfvdValueGreenPort M kappa omega s
        (canonicalSeededEnrichedTfvdGenuinePort kappa omega s) =
      finiteC3GenuineBracketGreenBoundaryPair (M * 3) s := by
  rw [finiteC3GenuineBracketGreenBoundaryPair_eq_greenBoundaryPair]
  apply Prod.ext
  · ext n
    let mr := finProdFinEquiv.symm n
    have hn : finProdFinEquiv mr = n :=
      finProdFinEquiv.apply_symm_apply n
    obtain ⟨m, r⟩ := mr
    rw [← hn]
    simp only [canonicalSeededEnrichedTfvdGenuinePort]
    rw [finiteC3EnrichedTfvdValueGreenPort_fst_finProd,
      enrichedAngularTfvdCoordinateToCpGreenTriple_eq_canonical
        3 hkappa omega m (homega m) s]
    fin_cases r <;>
      simp [canonicalCpGreenTfvdTriple,
        tfvdDecode_canonicalCpGreenTfvdCoordinate,
        finiteC3GreenBoundaryPair, finProdFinEquiv, Nat.add_comm]
  · ext n
    let mr := finProdFinEquiv.symm n
    have hn : finProdFinEquiv mr = n :=
      finProdFinEquiv.apply_symm_apply n
    obtain ⟨m, r⟩ := mr
    rw [← hn]
    simp only [canonicalSeededEnrichedTfvdGenuinePort]
    rw [finiteC3EnrichedTfvdValueGreenPort_snd_finProd,
      enrichedAngularTfvdCoordinateToCpGreenTriple_eq_canonical
        3 hkappa omega m (homega m) s]
    fin_cases r <;>
      simp [canonicalCpGreenTfvdTriple,
        tfvdDecode_canonicalCpGreenTfvdCoordinate,
        finiteC3GreenBoundaryPair, finProdFinEquiv, Nat.add_comm]

/-- The pair-level boundary form specializes exactly to the existing
canonical seeded TFVD boundary form. -/
theorem finiteC3EnrichedTfvdPairBoundaryForm_canonical
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ) (s : ℂ) :
    finiteC3EnrichedTfvdPairBoundaryForm M
        (finiteC3EnrichedTfvdPairTransport M kappa omega s
          (canonicalEnrichedTfvdValueLogJetPair kappa omega s)) =
      finiteCanonicalSeededTfvdSameSBoundaryForm M kappa omega s := by
  unfold finiteC3EnrichedTfvdPairBoundaryForm
    finiteCanonicalSeededTfvdSameSBoundaryForm
    finiteCanonicalEnrichedTfvdSameSBoundaryTrace
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro m hm
  have hlt : m < M := Finset.mem_range.mp hm
  simp [hlt, finiteC3EnrichedTfvdPairTransport,
    canonicalEnrichedTfvdValueLogJetPair,
    canonicalSeededEnrichedTfvdGenuinePort,
    canonicalSeededEnrichedTfvdLogJetPort,
    canonicalEnrichedTfvdSameSBoundaryCells]

/-- Universal canonical transport theorem.  The same enriched input yields
the Genuine value chart, its log-jet readout, and the full C3 Green port. -/
theorem finiteC3EnrichedTfvdPairTransport_canonical
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    let data := finiteC3EnrichedTfvdPairTransport M kappa omega s
      (canonicalEnrichedTfvdValueLogJetPair kappa omega s)
    (data.valueReadout = finiteBracketedDirichletChart 3 M s) ∧
    (data.logJetReadout = finiteCanonicalLogBracketChart M s) ∧
    (data.greenPort =
      finiteC3GenuineBracketGreenBoundaryPair (M * 3) s) := by
  dsimp [finiteC3EnrichedTfvdPairTransport,
    canonicalEnrichedTfvdValueLogJetPair]
  exact
    ⟨finiteSeededEnrichedTfvdGenuineReadout_canonical
        M hkappa omega homega s,
      finiteSeededEnrichedTfvdGenuineReadout_canonicalLogJet
        M hkappa omega homega s,
      finiteC3EnrichedTfvdValueGreenPort_canonical
        M hkappa omega homega s⟩

/-- Pair-enriched Green transport identity, valid before any zero is
considered.  The same-parameter value/log-jet boundary form, after removing
its independently defined local provenance channels, is the Green form of
the two transported C3 ports at `s` and its reflection. -/
theorem finiteC3EnrichedTfvdPairBoundary_sub_provenance_eq_greenForm_transport
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    finiteC3EnrichedTfvdPairBoundaryForm M
          (finiteC3EnrichedTfvdPairTransport M kappa omega s
            (canonicalEnrichedTfvdValueLogJetPair kappa omega s)) -
        finiteCanonicalTfvdSameSGreenProvenanceDefect 3 M s =
      greenForm
        (finiteC3EnrichedTfvdPairTransport M kappa omega s
          (canonicalEnrichedTfvdValueLogJetPair kappa omega s)).greenPort
        (finiteC3EnrichedTfvdPairTransport M kappa omega
          (reflectedParameter s)
          (canonicalEnrichedTfvdValueLogJetPair
            kappa omega (reflectedParameter s))).greenPort := by
  rw [finiteC3EnrichedTfvdPairBoundaryForm_canonical]
  change
    finiteCanonicalSeededTfvdSameSBoundaryForm M kappa omega s -
        finiteCanonicalTfvdSameSGreenProvenanceDefect 3 M s =
      greenForm
        (finiteC3EnrichedTfvdValueGreenPort M kappa omega s
          (canonicalSeededEnrichedTfvdGenuinePort kappa omega s))
        (finiteC3EnrichedTfvdValueGreenPort M kappa omega
          (reflectedParameter s)
          (canonicalSeededEnrichedTfvdGenuinePort
            kappa omega (reflectedParameter s)))
  rw [
    finiteC3EnrichedTfvdValueGreenPort_canonical
      M hkappa omega homega s,
    finiteC3EnrichedTfvdValueGreenPort_canonical
      M hkappa omega homega (reflectedParameter s)]
  rw [Nat.mul_comm M 3]
  exact finiteCanonicalSeededTfvdBoundary_sub_provenance_eq_genuineGreenForm
    M hkappa omega homega s

/-- On the arithmetic pair, the universal leg-by-leg provenance specializes
exactly to the previously constructed canonical provenance defect.  Thus the
universal transport has not introduced a new residual under another name. -/
theorem finiteC3EnrichedTfvdPairGreenProvenance_canonical
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0) (s : ℂ) :
    let pair := canonicalEnrichedTfvdValueLogJetPair kappa omega s
    let reflectedPair := canonicalEnrichedTfvdValueLogJetPair
      kappa omega (reflectedParameter s)
    let direct := finiteC3EnrichedTfvdPairTransport
      M kappa omega s pair
    let reflected := finiteC3EnrichedTfvdPairTransport
      M kappa omega (reflectedParameter s) reflectedPair
    finiteC3EnrichedTfvdPairGreenProvenance
        M kappa omega pair direct reflected =
      finiteCanonicalTfvdSameSGreenProvenanceDefect 3 M s := by
  dsimp only
  let direct := finiteC3EnrichedTfvdPairTransport M kappa omega s
    (canonicalEnrichedTfvdValueLogJetPair kappa omega s)
  let reflected := finiteC3EnrichedTfvdPairTransport M kappa omega
    (reflectedParameter s)
    (canonicalEnrichedTfvdValueLogJetPair
      kappa omega (reflectedParameter s))
  have huniversal :=
    finiteC3EnrichedTfvdPairBoundary_eq_greenForm_add_provenance
      M kappa omega s
        (canonicalEnrichedTfvdValueLogJetPair kappa omega s)
        (canonicalEnrichedTfvdValueLogJetPair
          kappa omega (reflectedParameter s))
  have hcanonical :=
    finiteC3EnrichedTfvdPairBoundary_sub_provenance_eq_greenForm_transport
      M hkappa omega homega s
  change
    finiteC3EnrichedTfvdPairGreenProvenance M kappa omega
        (canonicalEnrichedTfvdValueLogJetPair kappa omega s)
        direct reflected =
      finiteCanonicalTfvdSameSGreenProvenanceDefect 3 M s
  change
    finiteC3EnrichedTfvdPairBoundaryForm M direct =
      greenForm direct.greenPort reflected.greenPort +
        finiteC3EnrichedTfvdPairGreenProvenance M kappa omega
          (canonicalEnrichedTfvdValueLogJetPair kappa omega s)
          direct reflected at huniversal
  change
    finiteC3EnrichedTfvdPairBoundaryForm M direct -
        finiteCanonicalTfvdSameSGreenProvenanceDefect 3 M s =
      greenForm direct.greenPort reflected.greenPort at hcanonical
  calc
    finiteC3EnrichedTfvdPairGreenProvenance M kappa omega
          (canonicalEnrichedTfvdValueLogJetPair kappa omega s)
          direct reflected =
        finiteC3EnrichedTfvdPairBoundaryForm M direct -
          greenForm direct.greenPort reflected.greenPort := by
      rw [huniversal]
      ring
    _ = finiteCanonicalTfvdSameSGreenProvenanceDefect 3 M s := by
      rw [← hcanonical]
      ring

end

end NativeCarryC3Crosswalk
