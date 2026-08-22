# Completed TFVD ledger to the C3 Green and gamma identities

This checkpoint keeps the completed TFVD data uncollapsed until the Green
form has been assembled. It proves two independent arrows and records the
remaining scalar boundary identification explicitly.

## 1. Source ledger to the provenance-preserving C3 Green form

For one complete C3 block, the canonical completed ledger retains

```text
ordinary gradient state
logarithmic-jet state
completed precompression residual
```

The Green boundary form is determined by the first two entries before the
residual-only rank-one collapse. The new source readout forms the two adjacent
same-parameter wedges directly from the ordinary and log-jet provenance legs.
Lean proves

```text
completedTfvdGreenLedgerSameSBoundaryCells
  (seededCompletedTfvdGreenLedger 1 s)
=
canonicalEnrichedTfvdSameSBoundaryCells
  tfvdHaarScale (fun _ => 1) 0 s.
```

After both the visible and dormant cells are retained, their total is exactly
the existing seeded TFVD boundary form. Subtracting the independently defined
provenance channels gives the reflected C3 Green form:

```math
\mathcal B_{\mathrm{ledger}}(s)-\mathcal P_{\mathrm{C3}}(s)
=
\mathrm{Green}
\left(B_3(s),B_3(s^\#)\right).
```

The corresponding theorem is

```lean
completedTfvdGreenLedgerSameSBoundary_sub_provenance_eq_greenForm
```

It has no zero, limit, critical-line, isotropic-membership, or scalar-kernel
hypothesis.

## 2. Faithful camera packing and the linear carry-time Green identity

The ordinary provenance leg also reconstructs the complete three-cell C3
boundary port before scalar synthesis. Lean proves

```lean
completedTfvdGreenLedgerC3Port_seeded
```

which identifies that reconstructed port literally with
`finiteC3GenuineBracketGreenBoundaryPair 3 s`.

The port is then packed into six all-bases camera coordinates using the
already-proved injective packing. In the open Genuine strip the resulting
camera state is nonzero. Away from the half-abscissa, its intrinsic complex
carry time is nonreal, so it can be supplied to the existing source gamma
field. Lean proves:

```lean
seededCompletedTfvdCarryGammaState_ne_zero
seededCompletedTfvdCarryGammaEnergy_pos
seededCompletedTfvdCarryGammaState_diagonal_green_identity
```

The last theorem is the exact operatorial identity

```math
2\,\mathrm{Im}(\lambda)
\left(\lVert\gamma_1\rVert^2+\lVert\gamma_2\rVert^2\right)
=
\mathrm{Green}_{21}-\mathrm{Green}_{12},
\qquad
\lambda=\mathrm{carryTime}(s),
```

with strictly positive gamma energy off the half-abscissa.

## Rank-one residual obstruction

None of these statements reconstructs the C3 port from the collapsed residual.
The existing theorem

```lean
map_seededCompletedTfvdGreenLedger_residual_eq_smul
```

shows that every real-linear image of that residual remains on one fixed ray.
The source-to-Green theorem therefore uses the uncollapsed ordinary and
log-jet channels, as required by the rank audit.

## Exact remaining scalar seam

This checkpoint does not identify the completed scalar value/log-jet
Wronskian with the raw diagonal Gram `c3RawGammaGram M s s`. The Green form
proved here pairs the direct state at `s` with the reflected state at `s#` and
retains the completion/provenance channels. The remaining construction must
identify the completed scalar boundary traces with the boundary coordinates
of this already-proved operatorial Green realization, or with the corresponding
completed product state used by the self-adjoint-operator repository.

Consequently the older interface

```lean
FiniteC3CompletedGreenWronskianSeam
```

remains a sufficient conditional capstone, not a theorem asserted by this
checkpoint. The new results prove the full-ledger source-to-Green and
linear-carry-time energy arrows without silently replacing the reflected
kernel by a raw diagonal one.
