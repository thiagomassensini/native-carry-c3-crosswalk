# Finite-chart / Green transport audit

## Question

Can the finite C3 Genuine chart be identified, before any zero hypothesis,
with the reflected Green form plus its aligned outer endpoint?

All objects below use exactly `M` C3 blocks, `3M` Green edges, and the outer
vertex `3M`. No reindexing or implicit sign convention is used.

## The linear identity

The finite chart already has the desired transport shape in the linear TFVD
port:

```math
\boxed{
\mathrm{FiniteChart}_{3,M}(s)
=\mathrm{AngularTrace}_M(s)+(3M+1)^{-s}.
}
```

This identity is universal. Both summands are linear in the Dirichlet state.
It is the kernel-checked wrapper
`finiteC3Chart_eq_angularTrace_add_linearOuter` around the existing angular
port theorem.

## The reflected Green balance

The reflected `greenForm` is not the angular trace. It is a bilinear
Wronskian formed from the direct and reflected boundary pairs. Resolving the
existing finite ledger without hiding a sign gives

```math
\boxed{
\mathrm{FiniteChart}_{3,M}(s)
+\mathrm{CoupledGreen}_{3,M}(s)
=\mathrm{greenForm}_{3M}(s,s^\#)
+\mathrm{Outer}_{3M}(s).
}
```

Therefore

```math
\boxed{
\mathrm{FiniteChart}_{3,M}(s)
=\mathrm{greenForm}_{3M}(s,s^\#)
+\mathrm{Outer}_{3M}(s)
\iff
\mathrm{CoupledGreen}_{3,M}(s)=0.
}
```

The proposed identity is consequently equivalent to the coupled Green
closure; it is not an earlier transport identity from which that closure can
be derived.

## Adding the nonlocal tail

Let `T_{3,M}` be the canonical unresolved tail and let

```math
R^{\mathrm{tail}}_{3,M}
=\mathrm{Outer}_{3M}+T_{3,M}.
```

The exact completed balance is

```math
\boxed{
(\mathrm{FiniteChart}_{3,M}+T_{3,M})
+\mathrm{CoupledGreen}_{3,M}
=\mathrm{greenForm}_{3M}+R^{\mathrm{tail}}_{3,M}.
}
```

Thus adding the same tail to both readings does not remove the coupled flux:

```math
\mathrm{FiniteChart}_{3,M}+T_{3,M}
=\mathrm{greenForm}_{3M}+R^{\mathrm{tail}}_{3,M}
\iff
\mathrm{CoupledGreen}_{3,M}=0.
```

At a Genuine zero, the completed chart vanishes, so the exact conclusion is

```math
\mathrm{CoupledGreen}_{3,M}
=\mathrm{greenForm}_{3M}+R^{\mathrm{tail}}_{3,M},
```

not that the right-hand side already vanishes.

## Internal-strip obstruction

The distinction is not only formal. At the real critical parameter
`s = 1 / 2`, the reflected Green form is zero at every cutoff because its
radial factor vanishes. If the proposed chart/Green equality held at every
cutoff, the finite charts would equal the reflected outer endpoints. Passing
to the limit would force the infinite C3 chart, and hence Genuine, to vanish.

The existing real-axis positivity theorem proves instead that Genuine is
nonzero at `1 / 2`. Lean therefore derives

```math
\exists M,\qquad
\mathrm{FiniteChart}_{3,M}(1/2)
\ne
\mathrm{greenForm}_{3M}(1/2,1/2)
+\mathrm{Outer}_{3M}(1/2).
```

This counterexample lies inside the open Genuine strip and on the canonical
arithmetic curve.

## Consequence for the next bridge

The viable target is not an equality between the linear scalar readout and
the bilinear Wronskian. It is a typed transport from the linear angular port
into boundary data that preserves the additional log-jet/return coordinate
before the Green pairing is formed. The independent coupled Green term marks
exactly the information that such a transport must account for.

## Public declarations

```lean
finiteC3Chart_eq_angularTrace_add_linearOuter
finiteC3Chart_add_coupledGreen_eq_greenForm_add_outer
finiteC3Chart_eq_greenForm_add_outer_iff_coupledGreen_eq_zero
finiteC3TailCompletedChart_add_coupledGreen_eq_greenForm_add_boundary
finiteC3TailCompletedChart_eq_greenForm_add_boundary_iff_coupledGreen_eq_zero
exists_cutoff_finiteC3Chart_ne_greenForm_add_outer_at_realHalf
```
