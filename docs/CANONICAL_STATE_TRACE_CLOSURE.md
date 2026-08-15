# Canonical-state trace closure

This module identifies the analytic regularity statement behind closure of
the enriched C3 TFVD port. It introduces no new zero predicate, Green
operator, inverse, or confinement hypothesis.

## Geometry before zeros

For a prime camera `p`, a positive cutoff `M`, and a parameter `s` in the
open Genuine strip, let

```math
\mathcal D_p(s)
=
\mathrm{structuralCarryGreenDefectEnergy}(p,s).
```

Let `m_M(s)` be the canonical all-prime mass endpoint and let `J_arith` be
the already constructed closed arithmetic nonlocal
trace. Lean proves, without assuming a zero,

```math
\boxed{
\mathcal D_p(s)=0
\quad\Longleftrightarrow\quad
m_M(s)\in\mathrm{dom}(J_{\mathrm{arith}}).
}
```

Both sides identify the same regularity condition

```math
\mathrm{Re}(s)=\frac12,
```

but the new theorem states this as a crosswalk between the geometric defect
and the explicit domain of a closed operator. The half-abscissa is a
consequence of the two independently constructed objects; it is not built
into a new definition.

The Lean declaration is

```lean
structuralCarryGreenDefectEnergy_eq_zero_iff_massState_mem_traceDomain
```

## Scalar zero and completed-port closure

Let `C_{N,p}(s)` denote the three-coordinate tail-completed readout.
At a scalar Genuine zero, its first two coordinates vanish and its norm is
exactly the structural defect energy. Lean now proves

```math
\boxed{
\mathcal C_{N,p}(s)=0
\quad\Longleftrightarrow\quad
m_M(s)\in\mathrm{dom}(J_{\mathrm{arith}}).
}
```

The tail cutoff `N` and trace cutoff `M` are independent because the
tail-defect coordinate is cutoff invariant.

The coercive companion says

```math
\left\lVert\mathcal C_{N,p}(s)\right\rVert>0
\quad\Longleftrightarrow\quad
m_M(s)\notin\mathrm{dom}(J_{\mathrm{arith}}).
```

The corresponding declarations are

```lean
c3EnrichedTailBranchCompletedReadout_eq_zero_iff_massState_mem_traceDomain
c3EnrichedTailBranchCompletedReadout_norm_pos_iff_massState_not_mem_traceDomain
```

## Multiplicity-one roots

The pinned CPFormal package already constructs a canonical global mass state
from the tangents of a simple Genuine root. It also defines the proposition
that its material vertical trace is square summable over the prime atlas.
The crosswalk proves that this existing state-specific regularity is exactly
membership of the canonical mass endpoint in the arithmetic trace domain:

```math
m_M(s)\in\mathrm{dom}(J_{\mathrm{arith}})
\quad\Longleftrightarrow\quad
\mathrm{SimpleRootMassVerticalGlobalTraceDomainAt}(M,s).
```

Consequently, at a simple Genuine root,

```math
\boxed{
\mathcal C_{N,p}(s)=0
\quad\Longleftrightarrow\quad
\text{the root-derived material trace is globally square summable}.
}
```

This is a concrete state-specific formulation of the remaining analytic
gate. It replaces the vague assertion that a scalar zero must somehow become
Green-isotropic with a precise regularity statement about an already
constructed canonical state.

The declarations are

```lean
massState_mem_traceDomain_iff_simpleRoot_globalTraceDomain
c3EnrichedTailBranchCompletedReadout_eq_zero_iff_simpleRoot_globalTraceDomain
simpleGenuineRoot_completedPort_traceClosure_capstone
```

## Exact scope

The module does **not** prove that every simple root satisfies the global
trace-domain condition. That implication would close the remaining
confinement gate and is not obtained from scalar vanishing, finite TFVD
reconstruction, or Pythagorean conservation alone.

The finite primitive real implementation is consistent with the downstream
geometry: it reconstructs

```math
f=G(Bf)+R(\mathrm{Tr}f)
```

in `R^2` and validates the saturated cameras. Its state, however, is defined
from the outset with amplitude `n^(-1/2)`. It therefore tests the
critical realization after the structural exponent has been selected; it
does not supply the missing off-critical trace-domain estimate.

Its `hidden_energy` diagnostic is the Cauchy complement of the scalar
resultant inside the finite coordinate tuple. Consequently, when the scalar
resultant vanishes, the hidden energy equals the full coordinate energy; it
does not vanish with the scalar. The finite diagnostic therefore supports
the enriched-carrier formulation and rules out treating scalar closure as
state closure. It does not replace the required cofinal trace estimate.
