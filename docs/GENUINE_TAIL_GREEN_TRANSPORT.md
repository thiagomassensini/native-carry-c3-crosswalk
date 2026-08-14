# Genuine tail transport into the Green ledger

## Purpose

The finite coarse-readout counterexample shows that vanishing of two scalar
syntheses does not characterize a Green-isotropic boundary relation. A
canonical Genuine state carries more information: at every cutoff, its finite
bracket chart and the unresolved tail are two pieces of one summable infinite
chart.

This module retains that nonlocal tail when the Genuine bracket is transported
to the C3 Green boundary pair. It does not assume that a scalar zero annihilates
the pure Green form.

## Enriched boundary and defect

For cutoff `M`, define the retained boundary correction

```math
R^{\mathrm{tail}}_{3,M}(s)
=
\mathrm{Outer}_{3M}(s)+T_{3,M}(s),
```

where `T` is the exact tail of the absolutely summable bracket series. The
tail-enriched Green defect is

```math
D^{\mathrm{tail}}_{3,M}(s)
=
\mathrm{CoupledGreen}_{3,M}(s)
-\left(
  \mathrm{greenForm}\left(B^{\mathrm G}_{3M}(s),B^{\mathrm G}_{3M}(s^\#)\right)
  +R^{\mathrm{tail}}_{3,M}(s)
\right).
```

The existing finite Green ledger and the exact head--tail decomposition give,
first, the finite equality

```math
\boxed{
D^{\mathrm{tail}}_{3,M}(s)
=-\left(\mathrm{BracketChart}_{3,M}(s)+T_{3,M}(s)\right).
}
```

Thus the retained correction is literally `Outer + Tail`, while the defect is
the coupled flux minus `Green form + Outer + Tail`. The minus sign above comes
from that subtraction; it is not an additional normalization.

The exact head--tail decomposition then gives, for every cutoff and before any
zero hypothesis,

```math
\boxed{
D^{\mathrm{tail}}_{3,M}(s)
=-\mathrm{BracketChart}_{3,\infty}(s).
}
```

Hence the enriched defect is independent of `M`. In the open Genuine strip,
the chart factorization gives the stronger identity

```math
\boxed{
D^{\mathrm{tail}}_{3,M}(s)
=-a_3(s)\,\mathrm{Genuine}(s).
}
```

The factor `a₃(s)` is already proved nonzero there. Therefore

```math
D^{\mathrm{tail}}_{3,M}(s)=0
\quad\Longleftrightarrow\quad
\mathrm{Genuine}(s)=0
```

at any one cutoff, and equivalently at every cutoff.

## Green-language kernel property

At a Genuine zero, Lean obtains the exact finite identity

```math
\mathrm{CoupledGreen}_{3,M}(s)
=
\mathrm{greenForm}\left(B^{\mathrm G}_{3M}(s),B^{\mathrm G}_{3M}(s^\#)\right)
+\mathrm{Outer}_{3M}(s)+T_{3,M}(s).
```

Both retained boundary pieces tend to zero. Consequently the coupled Green
ledger and the pure bracket-resolved Green form become asymptotically equal.
The theorem deliberately does not claim that their common limit is zero.

This distinguishes the canonical curve from an arbitrary vector killed by one
finite synthesis: the canonical point carries one cutoff-independent defect
and a tail determined by the same infinite arithmetic state.

## Logical boundary

The result transports the Genuine kernel exactly into a nonlocal Green ledger,
but it does not prove membership in the fixed diagonal Green relation. Such
membership would annihilate the pure Green form and remains equivalent to the
separately audited confinement frontier.

No theorem in this module assumes:

- critical displacement zero;
- pure Green closure;
- isotropic membership;
- strong Genuine nonvanishing;
- a chosen inverse or pseudoinverse.

## Public declarations

```lean
finiteC3GenuineTailGreenBoundary
finiteC3GenuineTailGreenDefect
finiteC3GenuineTailGreenDefect_eq_neg_finiteChart_add_tail
finiteC3GenuineTailGreenDefect_eq_neg_chart
finiteC3GenuineTailGreenDefect_cutoff_invariant
finiteC3GenuineTailGreenDefect_eq_neg_factor_mul_genuine
finiteC3GenuineTailGreenDefect_eq_zero_iff_genuine_zero
finiteC3TailResolvedGreenIdentity_of_genuine_zero
finiteC3TailResolvedGreenIdentity_iff_genuine_zero
finiteC3GenuineTailGreenBoundary_tendsto_zero
finiteC3CoupledGreenFlux_sub_greenForm_tendsto_zero_of_genuine_zero
IsC3TailCoherentGreenKernelPoint
isC3TailCoherentGreenKernelPoint_iff_genuine_zero
```
