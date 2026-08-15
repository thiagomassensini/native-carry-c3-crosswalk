# Arithmetic linear-kernel audit

This audit tests the proposed implication

```math
\ker(\mathrm{stateReadout})
\subseteq
\ker(\mathrm{GreenBulk})
```

on the universal linear carriers already present in the C3 crosswalk.

## Minimal joint carrier

The finite minimal-provenance construction retains both the coarse
two-scalar readout and the complete Green port. Lean internalizes the existing
two-cell coarse-kernel witness in that joint carrier and proves

```math
\ker(\mathrm{finiteC3ArithmeticStateReadout})
\not\subseteq
\ker(\mathrm{finiteC3ArithmeticBulk}).
```

The complete Green leg therefore cannot be recovered from the coarse readout
by a universal linear kernel inclusion.

## Enriched TFVD transport

The obstruction is not caused by an incomplete cell or by omitting
provenance. For every complex parameter, Lean constructs a typed enriched
TFVD input with exterior seed `1`, one complete block, zero value readout, and
nonzero transported Green port.

This witness audits the universal transport domain. It is deliberately not
identified with the canonical Dirichlet value/log-jet pair.

## Remaining canonical-curve question

The only smaller locus not covered by these witnesses is the nonlinear
canonical arithmetic curve on which every block and the log jet arise from
one common Dirichlet parameter. Consequently, a successful theorem must use
a property specific to that curve. Adding the desired kernel inclusion as a
field of a new linear carrier would assume the missing result rather than
derive it.

## Public declarations

```text
finiteC3Arithmetic_readoutKernel_not_le_bulkKernel
exists_enrichedTfvdPairTransport_valueKernel_greenPort_nonzero
```
