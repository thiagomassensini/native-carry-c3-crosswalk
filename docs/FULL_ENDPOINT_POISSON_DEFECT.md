# Full endpoint, Poisson return, and structural defect

This checkpoint keeps the complete endpoint separate from scalar synthesis.

## Exact Poisson implication

For the normalized Green-frame split, Lean uses the existing exact Poisson
identity

```math
M(E x)=B x.
```

Consequently,

```math
E x=0 \Longrightarrow B x=0.
```

If a realization identifies the squared bulk norm with the structural
carry--Green defect energy, the established rigidity theorem gives

```math
E x=0
\Longrightarrow
\mathcal D_p(s)=0
\Longrightarrow
\mathrm{Re}(s)=\frac12.
```

Here `E x` is the complete normalized endpoint, not a scalar resultant.

## Complete finite C3 port

The C3 full state port retains the direct and reflected Green endpoints before
scalar synthesis. Its Green bulk is defined directly by the boundary form and
has the exact factorization

```math
\mathrm{Bulk}_{M}(s)
=
\mathrm{RadialDifference}_3(s)\,
\mathrm{ReflectedPairing}_{M}(s).
```

At every nonempty cutoff in the open strip, the reflected pairing is nonzero.
Thus zero full-port Green bulk forces zero structural defect energy and then
the half-abscissa.

## Scalar readout and full port

The canonical full C3 Green port is nonzero at every nonempty cutoff in the
open strip. At a Genuine zero, Lean proves both

```math
\mathrm{TailCompletedReadout}_{M}(s)=0
```

and

```math
\mathrm{FullGreenPort}_{M}(s)\ne0.
```

These statements distinguish scalar cancellation from the complete endpoint.
No implication from scalar readout zero to full endpoint zero is used.

## Public declarations

```text
normalizedFullEndpoint_zero_implies_bulk_zero
structuralDefect_zero_of_normalizedFullEndpoint_zero
re_eq_half_of_normalizedFullEndpoint_zero
c3FullStatePortGreenBulk_canonical
c3FullStatePortGreenBulk_eq_zero_of_fullEndpoint_zero
structuralDefect_zero_of_canonicalFullStateGreenBulk_zero
fullC3Endpoint_zero_structuralDefect_zero_re_eq_half
finiteC3GenuineFullGreenEndpoint_ne_zero
canonicalEnrichedTfvdFullStatePort_ne_zero
genuineZero_tailStateReadout_zero_fullStatePort_ne_zero
```
