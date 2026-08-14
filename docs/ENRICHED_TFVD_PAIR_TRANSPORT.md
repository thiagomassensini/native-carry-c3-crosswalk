# Enriched TFVD pair transport

## Why the carrier must be a pair

The finite Genuine chart is a linear scalar readout. The Green form is a
sesquilinear pairing of two boundary ports. A map from the synthesized scalar
alone therefore has the wrong arity and has already erased the block labels
needed by Green.

The finite carrier used here retains two seeded enriched ports:

~~~text
EnrichedTfvdValueLogJetPair
  value  : SeededEnrichedTfvdPort
  logJet : SeededEnrichedTfvdPort
~~~

Each block of either port retains its two visible TFVD coordinates and its
third dormant edge. No scalar synthesis occurs before the local boundary
pairing.

## The finite transport

For M angular blocks, finiteC3EnrichedTfvdPairTransport returns:

~~~text
valueReadout   : complex scalar
logJetReadout  : complex scalar
boundaryCells  : Fin M -> two local same-parameter wedges
greenPort      : complete two-leg C3 port on Fin (M * 3)
~~~

The block/residue map is the canonical equivalence

~~~math
\mathrm{Fin}(M)\times\mathrm{Fin}(3)
\simeq
\mathrm{Fin}(3M).
~~~

Every enriched value block is decoded, transported to its three C3 Green
coordinates, decoded again into the radial and horizontal boundary legs, and
only then flattened. No representative, pseudoinverse, or scalar
reconstruction is selected.

## Universal identity before arithmetic specialization

For arbitrary typed value/log-jet pairs x and y, Lean proves

~~~math
\boxed{
\mathcal B_M(x)
=
\mathcal G_M\!\left(J_M^{s}x,J_M^{s^\#}y\right)
+\mathcal P_M(x,y).
}
~~~

Here:

- B_M is formed from the two local same-parameter wedges of every block;
- G_M is the abstract Green form of the full direct/reflected C3 ports;
- P_M is an explicit provenance ledger.

The provenance ledger is not defined as the difference of the other two
global expressions. For every visible cell it contains four independently
defined leg transports. For every block it also retains the third Green cell
as a dormant compensation. The proof is first established as an eight-scalar
polynomial identity for one cell, then for one complete three-residue block,
and only then summed over the cutoff.

This theorem has no hypothesis involving a Genuine zero, the critical strip,
the critical line, vanishing tilt, isotropic membership, or strong
nonvanishing.

## Canonical arithmetic specialization

On the canonical arithmetic pair, the same transport recovers literally:

~~~math
\begin{aligned}
\mathrm{valueReadout}(J_M(s))
  &=\mathrm{FiniteChart}_{3,M}(s),\\
\mathrm{logJetReadout}(J_M(s))
  &=\mathrm{FiniteLogChart}_{M}(s),\\
\mathrm{greenPort}(J_M(s))
  &=B^{\mathrm G}_{3M}(s).
\end{aligned}
~~~

Lean also proves that the new arbitrary-pair provenance specializes exactly
to the pre-existing canonical
finiteCanonicalTfvdSameSGreenProvenanceDefect. Thus the generalized carrier
does not rename or hide a residual.

The resulting canonical transport identity is

~~~math
\boxed{
\mathcal B_M(s)-\mathcal P_M(s)
=
\mathrm{greenForm}\!\left(
  B^{\mathrm G}_{3M}(s),B^{\mathrm G}_{3M}(s^\#)\right).
}
~~~

## What this closes, and what it does not

This closes the finite carrier and arity problem. The Genuine and Green
readings now arise as projections of one provenance-preserving value/log-jet
construction; the transport is not a function of the scalar chart alone.

It does not prove that a zero of the scalar readout makes the corrected
boundary form vanish. That remaining implication would require a theorem
showing that the canonical completed value/log-jet state closes B_M - P_M in
the relevant limit, or equivalently that its transported port lands in the
fixed isotropic relation. Neither assertion is inserted into the transport
definition.

## Public declarations

~~~lean
EnrichedTfvdValueLogJetPair
FiniteC3EnrichedTfvdPairTransportData
finiteC3EnrichedTfvdPairTransport
sameSEdgeBoundaryWedge_eq_greenEdge_add_pairChannels
finiteC3EnrichedTfvdPair_blockBoundary_eq_greenEdges_add_provenance
sum_finiteC3GreenPortEdge_eq_sum_blocks
finiteC3EnrichedTfvdPairBoundary_eq_greenForm_add_provenance
finiteC3EnrichedTfvdValueGreenPort_canonical
finiteC3EnrichedTfvdPairTransport_canonical
finiteC3EnrichedTfvdPairBoundary_sub_provenance_eq_greenForm_transport
finiteC3EnrichedTfvdPairGreenProvenance_canonical
~~~
