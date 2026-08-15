# Branch / Green quadratic crosswalk

## Purpose

This module tests the noncompensation route on the enriched, nonlocal carrier.
It does not postulate that a Genuine zero closes the pure Green channel.
Instead, it asks what can be proved for arbitrary compatible parameters before
any zero is selected.

The answer has two parts:

1. the positional branch defect is an exact positive rescaling of the radial
   Green difference, with a fixed sign;
2. the complete tail defect and the positional defect can be retained as
   orthogonal coordinates of one real Hilbert readout.

## Exact branch-to-Green coefficient

Write

```math
\delta=\sigma-\frac12,
\qquad
q_p(\sigma)=p^{-2\sigma},
```

and define

```math
\tau_p(\sigma)
=p^{-\delta}\left(1-q_p(\sigma)\right)^{-1}.
```

For a prime `p` and `sigma > 0`, Lean proves

```math
\tau_p(\sigma)>0.
```

The existing branch defect and radial Green difference then satisfy the exact
identity

```math
\boxed{
\mathrm{branchDefect}(p,\sigma)
=-\tau_p(\sigma)\,
  \mathrm{cpRadialDifference}(p,\delta).
}
```

This is stronger than an equality of zero loci. It fixes the coefficient,
its sign, and its strict positivity without mentioning Genuine, a zero, or a
critical-line assumption.

## The enriched Pythagorean readout

Let

```math
D_M^{\mathrm{pair,tail}}(s)
```

be the already formalized complete enriched-pair tail defect, and let

```math
E_\infty(s)>0
```

be the existing reflected Green energy in the open strip. The new readout is
the three-dimensional real vector

```math
\mathcal C_{M,p}(s)=
\left(
  \tau_p(\mathrm{Re}(s))
    \mathrm{Re}\!\left(D_M^{\mathrm{pair,tail}}(s)\right),
  \tau_p(\mathrm{Re}(s))
    \mathrm{Im}\!\left(D_M^{\mathrm{pair,tail}}(s)\right),
  E_\infty(s)\,
    \mathrm{branchDefect}(p,\mathrm{Re}(s))
\right).
```

The first two coordinates retain the full complex tail defect. The third
retains the pre-existing positional defect in reflected-Green scale. No scalar
sum is taken between those channels.

Lean computes the inner product exactly:

```math
\boxed{
\left\lVert\mathcal C_{M,p}(s)\right\rVert^2
=\tau_p(\mathrm{Re}(s))^2
  \mathrm{normSq}\!\left(D_M^{\mathrm{pair,tail}}(s)\right)
 +\left(
   E_\infty(s)\,
   \mathrm{branchDefect}(p,\mathrm{Re}(s))
  \right)^2.
}
```

Consequently, the completed norm controls the positional coordinate directly:

```math
\left(
 E_\infty(s)\,
 \mathrm{branchDefect}(p,\mathrm{Re}(s))
\right)^2
\le
\left\lVert\mathcal C_{M,p}(s)\right\rVert^2.
```

This is genuine noncompensation: the carrier coordinate cannot cancel the
branch coordinate because the two contributions are orthogonal squares.

## Genuine substitution and cutoff invariance

In the open strip, the existing tail theorem gives

```math
D_M^{\mathrm{pair,tail}}(s)
=-a_3(s)\,\mathrm{Genuine}(s).
```

Substitution into the Pythagorean identity yields

```math
\left\lVert\mathcal C_{M,p}(s)\right\rVert^2
=\tau_p^2
  \mathrm{normSq}(a_3(s))
  \mathrm{normSq}(\mathrm{Genuine}(s))
 +\left(E_\infty(s)\,
   \mathrm{branchDefect}(p,\mathrm{Re}(s))\right)^2.
```

The same existing head--tail identity also proves that the completed readout
is independent of `M`. Thus this is already a projective nonlocal object, not
a finite Dirichlet-polynomial port.

## Exact kernel

The transfer coefficient, the C3 chart factor, and the reflected Green energy
are nonzero under the stated strip and prime hypotheses. Lean therefore proves

```math
\boxed{
\mathcal C_{M,p}(s)=0
\quad\Longleftrightarrow\quad
\mathrm{Genuine}(s)=0
\quad\mathrm{and}\quad
\mathrm{branchDefect}(p,\mathrm{Re}(s))=0.
}
```

Composing with the frozen carry-geometry rigidity theorem gives the purely
positional formulation

```math
\boxed{
\mathcal C_{M,p}(s)=0
\quad\Longleftrightarrow\quad
\mathrm{Genuine}(s)=0
\quad\mathrm{and}\quad
\mathrm{C3Compatible}(\mathrm{Re}(s)).
}
```

## Exact remaining gate

Suppose the complete tail defect vanishes. The existing kernel theorem then
gives a Genuine zero, so the first two coordinates of the completed vector
vanish. Lean proves exactly

```math
\boxed{
D_M^{\mathrm{pair,tail}}(s)=0
\quad\Longrightarrow\quad
\left[
  \mathcal C_{M,p}(s)=0
  \quad\Longleftrightarrow\quad
  \mathrm{C3Compatible}(\mathrm{Re}(s))
\right].
}
```

This is the strongest unconditional conclusion supplied by the direct-sum
construction. It prevents cancellation, identifies the third coordinate, and
proves its exact radial relation. It does not prove that scalar or tail closure
annihilates that independent coordinate. Treating that last implication as a
consequence of the norm identity would reintroduce the confinement statement
as an unstated premise.

## Public declarations

```lean
branchToGreenTransferCoefficient
branchToGreenTransferCoefficient_pos
branchDefect_eq_neg_transfer_mul_radialDifference
C0GenuineBranchCompletedSpace
c0GenuineBranchCompletedReadout
c0GenuineBranchCompletedReadout_norm_sq_eq_scaled_completedEnergy
c0GenuineBranchCompletedReadout_eq_zero_iff_genuine_and_compatible
C3EnrichedTailBranchCompletedSpace
c3EnrichedTailBranchCompletedReadout
c3EnrichedTailBranchCompletedReadout_norm_sq
c3EnrichedTailBranchCompletedReadout_norm_sq_eq_genuine_branch
c3EnrichedTailBranchCompletedReadout_cutoff_invariant
branchDefectGreenEnergy_sq_le_enrichedTailCompletedReadout_norm_sq
c3EnrichedTailBranchCompletedReadout_eq_zero_iff_genuine_and_compatible
c3EnrichedTailBranchCompletedReadout_eq_zero_iff_compatible_of_tailDefect_zero
```

The implementation is in
[`BranchGreenQuadraticCrosswalk.lean`](../NativeCarryC3Crosswalk/BranchGreenQuadraticCrosswalk.lean).
