# Enriched TFVD pair and nonlocal tail closure

## Question

The finite enriched transport keeps both the value and log-jet legs, all C3
residues, and the complete reflected Green port. The remaining question was
whether adding the canonical unresolved Genuine tail makes the boundary
defect factor through the Genuine readout before any zero is assumed.

It does.

## Tail-completed value readout

For the canonical enriched pair, define

```math
Q^{\mathrm{tail}}_M(s)
=Q_M(s)+T_M(s),
```

where `Q_M` is the value readout returned by the enriched transport and `T_M`
is the exact unresolved tail of the same C3 bracket series. Lean proves

```math
Q^{\mathrm{tail}}_M(s)
=\mathrm{BracketChart}_3(s)
=a_3(s)\,\mathrm{Genuine}(s).
```

The identity is cutoff-independent. The factor `a_3(s)` is independently
nonzero throughout the open Genuine strip.

## Pair-level boundary defect

The corrected pair boundary is formed before scalar synthesis:

```math
\mathcal B^{\mathrm{corr}}_M(s)
=\mathcal B^{\mathrm{pair}}_M(s)-\mathcal P_M(s).
```

Here `P_M` is the explicit provenance ledger of the enriched transport. Lean
first identifies this corrected boundary with the full reflected C3 Green
form:

```math
\mathcal B^{\mathrm{corr}}_M(s)
=\mathrm{greenForm}\left(B^{\mathrm G}_{3M}(s),
  B^{\mathrm G}_{3M}(s^\#)\right).
```

Retain also the independently defined nonlocal boundary

```math
R^{\mathrm{tail}}_M(s)
=\mathrm{Outer}_{3M}(s)+T_M(s).
```

The pair-tail defect is

```math
D^{\mathrm{pair,tail}}_M(s)
=\mathrm{CoupledGreen}_{3,M}(s)
-\left(\mathcal B^{\mathrm{corr}}_M(s)
  +R^{\mathrm{tail}}_M(s)\right).
```

Lean proves the universal factorization

```math
\boxed{
D^{\mathrm{pair,tail}}_M(s)
=-Q^{\mathrm{tail}}_M(s).
}
```

Consequently, in the open strip,

```math
\boxed{
D^{\mathrm{pair,tail}}_M(s)
=-a_3(s)\,\mathrm{Genuine}(s).
}
```

No zero, critical-line, tilt, isotropic-membership, or strong-nonvanishing
hypothesis occurs in this factorization.

## Exact kernel consequence

Since `a_3(s)` does not vanish,

```math
D^{\mathrm{pair,tail}}_M(s)=0
\quad\Longleftrightarrow\quad
\mathrm{Genuine}(s)=0.
```

Thus a Genuine zero closes the complete tail-resolved enriched-pair ledger at
every finite cutoff:

```math
\mathrm{CoupledGreen}_{3,M}(s)
=\mathcal B^{\mathrm{corr}}_M(s)
 +\mathrm{Outer}_{3M}(s)+T_M(s).
```

The outer endpoint and tail tend to zero, so the coupled Green reading and
the corrected pair boundary become asymptotically equal.

## Why this is not yet pure Green closure

The factorization above closes the complete nonlocal defect. It does not say
that either of the two asymptotically equal Green readings tends to zero.

Lean proves the exact frontier, without assuming a Genuine zero:

```math
\mathcal B^{\mathrm{corr}}_M(s)\longrightarrow0
\quad\Longleftrightarrow\quad
\mathrm{Re}(s)=\frac12.
```

It also proves that the uniform rule

```math
\mathrm{Genuine}(s)=0
\quad\Longrightarrow\quad
\mathcal B^{\mathrm{corr}}_M(s)\longrightarrow0
```

is equivalent to `GenuineStrongNonvanishingInStrip`. Therefore the enriched
pair removes the finite arity and provenance obstruction and supplies the
desired universal tail-defect factorization, but it does not make the final
zero-to-pure-Green activation a bookkeeping consequence.

## Exact audit of the attempted last step

The remaining asymptotic quantity can be computed, rather than postulated.
At a Genuine zero, Lean proves

```math
\mathrm{CoupledGreen}_{3,M}(s)
\longrightarrow
D_3\!\left(\mathrm{Re}(s)-\frac12\right)
\mathcal E_\infty(s),
```

where the reflected pairing `E_infinity(s)` is nonzero throughout the open
strip. Consequently,

```math
\boxed{
\mathrm{Genuine}(s)=0
\quad\Longrightarrow\quad
\left(
  \mathrm{CoupledGreen}_{3,M}(s)\longrightarrow0
  \iff
  \mathrm{Re}(s)=\frac12
\right).
}
```

This also rules out treating the angular correction as a disposable tail.
At a Genuine zero its unscaled limit is

```math
-\mathcal E_\infty(s)\ne0.
```

The endpoint plus unresolved bracket tail does vanish. The angular
correction does not: it cancels the nonzero reflected pairing inside the
scalar bracket ledger. Thus the exact first unproved implication remains the
activation of coupled-Green closure from a Genuine zero. The existing
factorizations compute what that implication would force, but do not prove it
without the strong-nonvanishing statement.

## Public declarations

```lean
finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary
finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary_eq_greenForm
finiteC3CanonicalEnrichedTfvdPairTailReadout
finiteC3CanonicalEnrichedTfvdPairTailReadout_eq_chart
finiteC3CanonicalEnrichedTfvdPairTailReadout_eq_factor_mul_genuine
finiteC3EnrichedTfvdPairTailDefect
finiteC3EnrichedTfvdPairTailDefect_eq_neg_tailReadout
finiteC3EnrichedTfvdPairTailDefect_eq_neg_factor_mul_genuine
finiteC3EnrichedTfvdPairTailDefect_eq_zero_iff_genuine_zero
finiteC3TailResolvedEnrichedTfvdPairIdentity_of_genuine_zero
finiteC3CoupledGreenFlux_sub_correctedPairBoundary_tendsto_zero_of_genuine_zero
finiteC3CoupledGreenFlux_tendsto_radialBulk_of_genuine_zero
finiteCanonicalAngularGreenCorrection_not_tendsto_zero_of_genuine_zero
finiteC3CoupledGreenFlux_tendsto_zero_iff_re_eq_half_of_genuine_zero
C3EnrichedTfvdCorrectedPairBoundaryClosesAt
c3EnrichedTfvdCorrectedPairBoundaryClosesAt_iff_re_eq_half
genuineZerosCloseC3EnrichedTfvdCorrectedPairBoundary_iff_strongNonvanishing
```
