# Native Carry C3 Crosswalk

[![Lean theorem audit](https://github.com/thiagomassensini/native-carry-c3-crosswalk/actions/workflows/lean-audit.yml/badge.svg)](https://github.com/thiagomassensini/native-carry-c3-crosswalk/actions/workflows/lean-audit.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21935705.svg)](https://doi.org/10.5281/zenodo.21935705)

Version `0.3.0` · Lean/Mathlib `v4.32.0` · MIT licensed

Lean 4 integration layer proving that the pinned finite native real operator
and the pinned finite bracket characteristic are literally the same finite
computation in two coordinate presentations. It also materializes the exact
fifth-order C3 boundary correction, its first two time derivatives, the exact
stationary equation used by the certified residual ledgers, and the rigorous
promotion from a concrete interval certificate to a unique stationary-root
family.

The construction introduces no new zero predicate, analytic continuation,
limit hypothesis, or spectral assumption. Version `0.3.0` additionally formalizes the relational bracket law, the
multiplicity-independent analytic-order reduction, a canonical finite C3
spectral certificate, and the exact polarized two-variable raw C3
Green--gamma identity. It also proves that the uncalibrated raw positive
Cauchy readout is not the completed Genuine logarithmic derivative and keeps
the completed trace identity as the explicit remaining gate.

The latest form-first bridge also keeps the native target in its original
two-coordinate real plane. The C3 complex notation is used only through the
already-proved coordinate equivalence, and the finite prime-camera core is
embedded into the intrinsic all-bases Gram core before completion.


## Global relational bracket law

The common invariant is now packaged explicitly across the native real,
analytic bracket, Genuine, TFVD, Green, structural-energy, and arithmetic
trace presentations. Lean distinguishes the scalar bracket value, which a
Genuine zero annihilates, from the differentiated Green bracket, whose
closure is exactly zero tilt.

Pointwise, the closed-trace domain, maximal Green-isotropic graph, Green
bracket closure, vanishing structural defect, and `Re(s) = 1/2`
are equivalent presentations. Globally, activating trace admissibility or
Green-bracket closure at every Genuine zero is proved equivalent to
GenuineStrongNonvanishingInStrip. No activation implication is assumed.

The statements and exact scope are recorded in the
[global relational law of the bracket](docs/BRACKET_GLOBAL_RELATIONAL_LAW.md).

## Camera-complete cutoffs

Finite native cutoffs are now exposed explicitly as cutoffs by complete
bracket centers. A retained center always includes every camera radius and
both legs. The exact last positive index is

~~~math
H_2(M)=4M+1
~~~

for the aligned C2 camera, and

~~~math
H_b(M)=bM+\left\lfloor\frac b2\right\rfloor,
\qquad b\ge3,
~~~

for a natural camera. Hence a high-base camera is active at a raw horizon
`N` only after at least one whole cell fits:

~~~math
N\ge b+\left\lfloor\frac b2\right\rfloor.
~~~

For an initial atlas through `B`, the common camera-complete horizon for `M`
centers is

~~~math
\max\left(4M+1,\;BM+\left\lfloor\frac B2\right\rfloor\right).
~~~

The analytic remainder is also kept at the same geometric arity. Lean proves
before any zero hypothesis that

~~~math
\text{complete finite head}
+\text{tail of complete omitted centers}
=\text{infinite camera}
=a_b(s)Z_{\mathrm{native}}(s).
~~~

For even cameras, the final antipodal point is recorded with finite
coefficient `1`; the second incidence belongs to the first omitted center
and raises the infinite periodic coefficient to `2`. This endpoint is not
discarded or hidden by normalization.

This closes the cutoff-completeness issue and rules out artificial defects
from severed legs. It does not assume that a scalar zero annihilates the
remaining central Green defect: noncompensation of that enriched channel is
still a distinct analytic gate.

The definitions, exact head--tail ledger, and scope audit are in
[geometric cutoff completeness](docs/GEOMETRIC_CUTOFF_COMPLETENESS.md).

## C0 Genuine readout and the exact Green ledger

The historical C2 vertical factor `C0` is exposed using the pinned
`pairedBridgeFactor` definition. Lean reuses its nonvanishing theorem on the
open Genuine strip and constructs the nonzero camera dressing

```math
d_{0\leftarrow3}(s)=\frac{C_0(s)}{a_3(s)},
```

where `a₃` is the canonical C3 chart factor. Dressing the finite C3 angular
trace by this ratio produces a trace converging exactly to

```math
C_0(s)\,\mathrm{Genuine}(s).
```

The Green form is sesquilinear, so its type-correct comparison is the
reflected product of the direct and reflected C0 traces. For every complex
parameter and every finite cutoff, Lean proves the unconditional identity

```math
\boxed{
r_3(s)P_{0,M}(s)
=
\overline{d_{0\leftarrow3}(s)}\,d_{0\leftarrow3}(s^\#)
\left(G_{3M}(s)+r_3(s)R_M(s)\right).
}
```

Here `G` is the bracket-resolved reflected Green form and `R` is the complete
angular provenance correction already present in the scalar ledger. There is
no zero or critical-line hypothesis in this equality.

Since both dressings are nonzero in the strip, the corresponding pure-Green
equality holds exactly when `r₃(s) R_M(s) = 0`. Thus `C0 ≠ 0` lets Lean
cancel the vertical normalization, but it cannot delete the provenance term.
An explicit two-cell witness also proves that no defect detecting the fixed
diagonal Green relation can factor through the two C0-dressed coarse scalars
alone.

The exact statement, types, and finite obstruction are recorded in the
[C0 Genuine / Green boundary audit](docs/C0_GENUINE_GREEN_BOUNDARY_AUDIT.md).

The central public declarations are

```lean
c0VerticalFactor_ne_zero
c0ToC3BoundaryDressing_ne_zero
finiteC0GenuineBoundaryTrace_tendsto
finiteC0GenuineBoundaryPairing_tendsto
radialScaledAngularScalarPairing_eq_greenForm_add_correction
radialScaledC0GenuineBoundaryPairing_eq_dressedGreen_add_correction
radialScaledC0GenuineBoundaryPairing_eq_pureGreen_iff_correction_eq_zero
no_finiteC3_boundaryDefect_factorization_through_c0GenuineReadout
```

## Quadratic C0--Genuine / Green frontier

Keeping the scalar C0-dressed readout and the radial Green defect as
orthogonal coordinates gives the exact completed energy

```math
\mathcal E_{p}(s)
=
\mathrm{normSq}\!\left(C_0(s)\,\mathrm{Genuine}(s)\right)
+
\left(r_p(\delta)\,E_{\mathrm{Green}}(s)\right)^2,
\qquad
\delta=\mathrm{Re}(s)-\frac12.
```

This is an unconditional sum-of-squares identity. In the open strip, Lean
proves the quantitative lower bound

```math
\left(
2|\delta|\log(p)\,E_{\mathrm{Green}}(s)
\right)^2
\le \mathcal E_p(s),
```

and the exact kernel

```math
\mathcal E_p(s)=0
\quad\Longleftrightarrow\quad
\mathrm{Genuine}(s)=0
\quad\mathrm{and}\quad
\mathrm{Re}(s)=\frac12.
```

The logical distinction is explicit. If one hypothetically supplies a
scalar Genuine zero away from the half-abscissa, its completed energy is not
zero: it is exactly the strictly positive Green-defect square. Therefore the
quadratic identity proves confinement of the completed port, but it does not
silently turn scalar Genuine closure into completed-port closure. Lean also
proves that requiring this last implication for every Genuine zero is
equivalent to `GenuineStrongNonvanishingInStrip`.

The full statement and circularity audit are in the
[quadratic C0--Genuine / Green frontier](docs/C0_GENUINE_GREEN_QUADRATIC_FRONTIER.md).

The principal declarations are

```lean
c0GenuineGreenCompletedEnergy_eq_sum_of_squares
c0GenuineGreenCompletedEnergy_ge_radial_coercive_square
c0GenuineGreenCompletedEnergy_eq_zero_iff_re_eq_half
c0GenuineGreenCompletedEnergy_eq_greenDefect_sq_of_genuine_zero
c0GenuineGreenCompletedEnergy_pos_of_genuine_zero_off_critical
genuineZerosCloseC0GenuineGreenCompletedEnergy_iff_strongNonvanishing
```

## Canonical nonlocal arithmetic trace

The global prime-camera bridge is now packaged as a genuine unbounded
operator rather than a graph predicate or a chosen inverse. On

~~~math
H_{\mathrm{mass}}=\ell^2(\mathbb P;\mathbb R),
~~~

Lean first constructs the bounded injective damping

~~~math
R(v)_p=p^{-1/2}v_p
~~~

and defines

~~~math
J_{\mathrm{arith}}=R^{-1}
~~~

as Mathlib's maximal LinearPMap inverse. Its domain and action are exact:

~~~math
\mathcal D(J_{\mathrm{arith}})=
\left\{v\in H_{\mathrm{mass}}:
  \sum_p|\sqrt p\,v_p|^2<\infty
\right\},
\qquad
(J_{\mathrm{arith}}v)_p=\sqrt p\,v_p.
~~~

Lean proves that this operator is densely defined, closed, and self-adjoint.
Its graph is therefore a closed maximal Green-isotropic relation. The
enriched boundary port retains both coordinates

~~~math
v\longmapsto\left(v,J_{\mathrm{arith}}v\right),
~~~

and its concrete defect

~~~math
D_{\partial}(v,w)=w-J_{\mathrm{arith}}v
~~~

vanishes exactly on that fixed relation.

The finite intertwining is unconditional: the output of the trace on every
finite prime atlas is literally the existing provenance-preserving
Genuine-bracket/TFVD/Green readout. Globally, however, the trace is
necessarily partial. An explicit Lean witness has square-summable state and
centered bracket but a nonsummable p⁻¹/² trace flux. There is not even an
everywhere-defined function into ℓ² with the required coordinate formula.

The remaining arithmetic statement is exact and is not hidden in the new
definition:

~~~math
\mathrm{massState}(M,s)\in\mathcal D(J_{\mathrm{arith}})
\quad\Longleftrightarrow\quad
\mathrm{Re}(s)=\frac12
~~~

inside the open strip. Asking every Genuine zero to supply that domain
membership is proved equivalent to the existing
GenuineStrongNonvanishingInStrip frontier. The repository therefore does not
claim that implication as a new confinement proof.

At finite cutoff there is a second exact no-go. The provenance direction
((1,-1),0) is erased by coarse synthesis but does not belong to the fixed
diagonal relation. Hence a boundary defect that detects that relation cannot
factor through the two coarse Genuine scalars alone. A successful future
transport must carry nonlocal endpoint/tail data in addition to finite scalar
synthesis.

The complete type crosswalk, obstruction, and downstream gate are documented
in [the arithmetic nonlocal trace audit](docs/ARITHMETIC_NONLOCAL_TRACE_AUDIT.md).

The central public declarations are

~~~lean
arithmeticNonlocalTrace
mem_arithmeticNonlocalTrace_domain_iff
arithmeticNonlocalTrace_isClosed
arithmeticNonlocalTrace_isSelfAdjoint
arithmeticNonlocalBoundaryRelation_isMaximalGreenIsotropic
arithmeticBoundaryDefect_eq_zero_iff_mem_relation
arithmeticBoundaryDefect_nonlocalBoundaryPort
finiteArithmeticNonlocalBoundaryPort_mem_relation
arithmeticFiniteTrace_intertwines_enrichedBracketTfvdGreen
no_everywhere_globalPrimeVerticalTrace
no_finiteC3_boundaryDefect_factorization_through_coarse
genuineZero_to_arithmeticNonlocalTrace_domain_iff_strongNonvanishing
~~~

## Genuine control of the existing quadratic carry energy

No new norm is needed for the coercive side of noncompensation. For every
nonempty cutoff and every prime camera, Lean proves

~~~math
\left\lVert
  \mathrm{primeGreenBulkFiniteState}(M,s,\{p\})
\right\rVert^2=0
\quad\Longleftrightarrow\quad
\mathrm{branchDefect}(p,\mathrm{Re}(s))=0
\quad\Longleftrightarrow\quad
\mathrm{Re}(s)=\frac12.
~~~

Thus one existing camera norm already detects the unique quadratic
equilibrium. The unresolved direction is the upper transport from the scalar
Genuine readout to that energy. The direct candidate is

~~~math
\kappa
\left\lVert
  \mathrm{primeGreenBulkFiniteState}(M,s,\{p\})
\right\rVert^2
\le
\mathrm{normSq}\!\left(a_3(s)\,\mathrm{Genuine}(s)\right),
\qquad \kappa>0.
~~~

At a Genuine zero, Lean proves that such a positive-coefficient estimate
holds if and only if `Re(s) = 1/2`. Requiring it at every Genuine zero is
therefore equivalent to `GenuineStrongNonvanishingInStrip`; it is not supplied
silently by the existing Pythagorean identity.

The uniform-atlas version is even more rigid. For every nonempty cutoff,

~~~math
\exists C\ge0,\ \forall S,\quad
\left\lVert
  \mathrm{primeGreenBulkFiniteState}(M,s,S)
\right\rVert^2
\le C\,\mathrm{normSq}\!\left(a_3(s)\,\mathrm{Genuine}(s)\right)
\quad\Longleftrightarrow\quad
\mathrm{Re}(s)=\frac12.
~~~

Off the half-abscissa, every proposed scalar majorant is exceeded by some
finite prime atlas. This establishes that the existing norm is the correct
detector and isolates the sole remaining theorem as scalar-to-Hilbert
noncompensation, rather than norm construction.

The exact statements and scope guard are documented in the
[Genuine carry-energy control audit](docs/GENUINE_CARRY_ENERGY_CONTROL_AUDIT.md).

The principal declarations are

~~~lean
primeGreenBulkSingletonEnergy_eq_zero_iff_branchDefect_eq_zero
primeGreenBulkSingletonEnergy_eq_zero_iff_re_eq_half
genuineReadoutCoercivelyControlsSingletonCarryEnergyAt_iff_re_eq_half_of_zero
genuineZerosHaveCoerciveSingletonCarryEnergyControl_iff_strongNonvanishing
genuineReadoutControlsPrimeGreenAtlasEnergyAt_iff_critical
exists_primeGreenAtlas_violating_genuineReadout_majorant_of_re_ne_half
~~~

## C3 zero versus foundational positional compatibility

The frozen `carry-geometry` kernel is now imported directly. Its existing
predicate supplies the first step without mentioning the half-abscissa:

~~~math
\mathrm{C3Compatible}(\sigma)
\quad:=\quad
\forall k>0,\qquad
\left(3^{-k\sigma}\right)^2=3^{-k}.
~~~

Its purely positional rigidity theorem gives the second step:

~~~math
\mathrm{C3Compatible}(\sigma)
\quad\Longleftrightarrow\quad
\sigma=\frac12.
~~~

The only new transport statement is then isolated verbatim:

~~~math
\mathrm{IsNativeC3Zero}(\sigma,t)
\quad\Longrightarrow\quad
\mathrm{C3Compatible}(\sigma).
~~~

Lean confirms that this formulation is minimal, but does not discharge it
from the foundational theorem. Globally on the open strip, it is equivalent
to each previously identified form of the remaining gate:

~~~math
\mathrm{C3ZerosPreserveGeometry}
\quad\Longleftrightarrow\quad
\mathrm{BoundaryClosurePreservesMass}
\quad\Longleftrightarrow\quad
\mathrm{NativeZeroRigidity}
\quad\Longleftrightarrow\quad
\mathrm{GenuineStrongNonvanishingInStrip}.
~~~

Thus the decomposition removes all unnecessary machinery from the statement,
but it does not turn scalar boundary cancellation into quadratic compatibility
for free. The conditional capstone is proved and no unconditional confinement
claim is made.

The complete logical audit is in the
[C3 positional-compatibility bridge](docs/C3_POSITIONAL_COMPATIBILITY_BRIDGE.md).

The principal declarations are

~~~lean
C3PositionalGeometryCompatible
c3PositionalGeometryCompatible_iff
C3OperatorZerosPreservePositionalGeometryInStrip
c3OperatorZero_implies_positionalCompatibility_iff_pointwise_zeroRigidity
c3OperatorZerosPreservePositionalGeometryInStrip_iff_strongNonvanishing
c3OperatorZero_positionalCompatibility_capstone
~~~

## Genuine bracket → TFVD → Green, before zeros

The direct construction remembered in the research chronology is now exposed
as one public crosswalk. Differentiate the local Genuine bracket identity and
resolve the center block against the bracket gradient. For C3, the first
boundary coordinate is

```math
g_3(s,n)=
\frac{1}{3}\,\nu_3(s)
\left(
  \nabla\mathrm{CenterBlock}_3(s,n)
  -\nabla\mathrm{Bracket}_3(s,n)
\right),
```

where `ν₃(s)` is the existing phase normalizer. Lean proves coordinate by
coordinate that this is exactly the C3 Green block gradient. If

```math
B_M^{\mathrm G}(s)=
\left(
  \bigl(g_3(s,n)\bigr)_{n<M},
  \bigl(\nabla^+(s,n)\bigr)_{n<M}
\right),
```

then, for every complex `s` and every finite cutoff `M`,

```math
\boxed{
\mathrm{greenForm}
\left(B_M^{\mathrm G}(s),B_M^{\mathrm G}(s^\#)\right)
=\mathcal W^{\mathrm{Genuine}}_{3,M}(s)
=\mathrm{TFVDDiagonal}_{3,M}(s)
}.
```

This is an identity of the bracket-resolved operator, the enriched TFVD
carrier, and the Green boundary form. It has no vanishing assumption, strip
hypothesis, limiting argument, or critical-line hypothesis.

The seeded construction gives the direct finite ledger involving the Genuine
chart:

```math
\boxed{
\mathrm{CoupledGreen}_{3,M}(s)
=\mathrm{greenForm}
  \left(B_{3M}^{\mathrm G}(s),B_{3M}^{\mathrm G}(s^\#)\right)
 +\mathrm{Outer}_{3M}(s)
 -\mathrm{GenuineChart}_{3,M}(s)
}.
```

Equivalently, the seeded TFVD boundary form minus its independently defined
local provenance channels is exactly the same Green form. The capstone states
the two readouts together: the scalar readout of the canonical seeded TFVD
port is the finite bracketed Genuine chart, while its corrected boundary
readout is the Genuine bracket Green form.

The central public theorems are

```lean
finiteC3GenuineBracketGreenBoundaryPair_fst_apply_eq_bracketResidual
finiteC3GenuineBracketGreenBoundaryPair_eq_greenBoundaryPair
greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_genuineFlux
greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_tfvdDiagonal
finiteCanonicalSeededTfvdBoundary_sub_provenance_eq_genuineGreenForm
finiteC3BracketCoupledGenuineGreenFlux_eq_greenForm_add_outer_sub_chart
finiteC3GenuineBracketTfvdGreen_capstone
```

The identity does not assert that a scalar chart value alone annihilates the
bilinear Green form: the endpoint and provenance terms remain explicit rather
than being hidden in a zero hypothesis.

## Nonlocal tail-coherent Green kernel

The finite coarse kernel contains vectors that do not arise from the canonical
arithmetic curve. To retain the property that distinguishes a Genuine point,
the Green ledger now keeps the exact unresolved tail of the same summable
bracket series. Define

```math
R^{\mathrm{tail}}_{3,M}(s)
=\mathrm{Outer}_{3M}(s)+T_{3,M}(s)
```

and subtract the pure Green form together with this retained boundary from the
coupled Green flux. Lean first checks the finite sum and its sign explicitly:

```math
D^{\mathrm{tail}}_{3,M}(s)
=-\left(\mathrm{BracketChart}_{3,M}(s)+T_{3,M}(s)\right).
```

The exact head--tail decomposition then proves, at every cutoff and before
assuming a zero,

```math
\boxed{
D^{\mathrm{tail}}_{3,M}(s)
=-a_3(s)\,\mathrm{Genuine}(s).
}
```

Thus the defect is cutoff-independent. Since `a₃` is nonzero in the open
strip, its kernel is exactly the Genuine kernel:

```math
D^{\mathrm{tail}}_{3,M}(s)=0
\quad\Longleftrightarrow\quad
\mathrm{Genuine}(s)=0.
```

At such a zero, the coupled Green ledger is exactly the bracket-resolved Green
form plus `Outer + Tail` at every finite cutoff. The retained boundary tends to
zero, so the two Green readings become asymptotically equal. This statement
does not assert that the pure Green form itself vanishes and introduces no
critical-line or isotropic-membership hypothesis.

The construction and its logical audit are documented in the
[Genuine tail / Green transport](docs/GENUINE_TAIL_GREEN_TRANSPORT.md).

The central declarations are

```lean
finiteC3GenuineTailGreenDefect_eq_neg_finiteChart_add_tail
finiteC3GenuineTailGreenDefect_eq_neg_chart
finiteC3GenuineTailGreenDefect_cutoff_invariant
finiteC3GenuineTailGreenDefect_eq_neg_factor_mul_genuine
finiteC3GenuineTailGreenDefect_eq_zero_iff_genuine_zero
finiteC3TailResolvedGreenIdentity_iff_genuine_zero
finiteC3GenuineTailGreenBoundary_tendsto_zero
finiteC3CoupledGreenFlux_sub_greenForm_tendsto_zero_of_genuine_zero
isC3TailCoherentGreenKernelPoint_iff_genuine_zero
```

## Finite-chart / Green transport audit

The exact identity having the linear shape suggested by the C3 bracket is

```math
\mathrm{FiniteChart}_{3,M}(s)
=\mathrm{AngularTrace}_M(s)+(3M+1)^{-s}.
```

Here both the angular trace and the outer value are linear in the Dirichlet
state. The reflected `greenForm`, by contrast, is a bilinear Wronskian. With
the already fixed aligned indices, Lean proves the sign-free finite balance

```math
\boxed{
\mathrm{FiniteChart}_{3,M}
+\mathrm{CoupledGreen}_{3,M}
=\mathrm{greenForm}_{3M}+\mathrm{Outer}_{3M}.
}
```

Consequently, replacing the angular trace by the reflected Green form is
equivalent to the closure statement itself:

```math
\mathrm{FiniteChart}_{3,M}
=\mathrm{greenForm}_{3M}+\mathrm{Outer}_{3M}
\quad\Longleftrightarrow\quad
\mathrm{CoupledGreen}_{3,M}=0.
```

Adding the canonical bracket tail to both sides does not change this
equivalence. Lean also proves, using real-axis positivity at
`s = 1 / 2`, that the proposed bilinear equality fails at some finite cutoff;
therefore it is not a universal transport identity on the canonical curve.

See the [finite-chart / Green transport audit](docs/FINITE_CHART_GREEN_TRANSPORT_AUDIT.md).

The public theorems are

```lean
finiteC3Chart_eq_angularTrace_add_linearOuter
finiteC3Chart_add_coupledGreen_eq_greenForm_add_outer
finiteC3Chart_eq_greenForm_add_outer_iff_coupledGreen_eq_zero
finiteC3TailCompletedChart_add_coupledGreen_eq_greenForm_add_boundary
finiteC3TailCompletedChart_eq_greenForm_add_boundary_iff_coupledGreen_eq_zero
exists_cutoff_finiteC3Chart_ne_greenForm_add_outer_at_realHalf
```

## Enriched value/log-jet transport

The finite-chart audit identifies an arity obstruction, not the end of the
Green route. The scalar chart has already erased the coordinates needed by a
bilinear boundary form. The corrected finite carrier therefore keeps the
seeded value port and the seeded log-jet port together, including the third
dormant edge of every C3 block.

Lean now constructs

```text
finiteC3EnrichedTfvdPairTransport
```

for arbitrary typed input pairs. Its output retains both scalar readouts, the
two local boundary cells of every block, and the complete two-leg Green port
on all `3M` residues. Before any arithmetic specialization, Lean proves the
universal identity

```math
\boxed{
\mathrm{PairBoundary}_M(x)
=\mathrm{greenForm}\!\left(J_M^s x,J_M^{s^\#}y\right)
+\mathrm{PairProvenance}_M(x,y).
}
```

The provenance term is built from four explicit leg transports per visible
cell and a separately retained dormant Green cell. It is not defined as a
global residual.

On the canonical arithmetic value/log-jet pair, the same `J_M` recovers
literally the finite Genuine chart, the finite log-jet chart, and the complete
bracket-resolved C3 Green port. Its universal provenance also specializes
exactly to the previously formalized canonical provenance defect.

No zero, strip, critical-line, tilt, isotropic-membership, or strong
nonvanishing hypothesis occurs in these transport theorems. The remaining
gate is narrower: a scalar Genuine zero does not by itself prove that the
corrected pair boundary `PairBoundary - PairProvenance` vanishes or that the
transported port belongs to the fixed isotropic relation.

See the [enriched TFVD pair transport audit](docs/ENRICHED_TFVD_PAIR_TRANSPORT.md).

The central declarations are

```lean
finiteC3EnrichedTfvdPairTransport
sameSEdgeBoundaryWedge_eq_greenEdge_add_pairChannels
finiteC3EnrichedTfvdPairBoundary_eq_greenForm_add_provenance
finiteC3EnrichedTfvdPairTransport_canonical
finiteC3EnrichedTfvdPairBoundary_sub_provenance_eq_greenForm_transport
finiteC3EnrichedTfvdPairGreenProvenance_canonical
```

### Nonlocal closure of the enriched pair

Completing the value readout with the unresolved tail of the same bracket
series produces a stronger universal identity. Define the corrected pair
boundary by subtracting its explicit provenance ledger and retain
`Outer + Tail` as the nonlocal boundary coordinate. Lean proves, for every
cutoff and before assuming a zero,

```math
\boxed{
D^{\mathrm{pair,tail}}_M(s)
=-\left(Q^{\mathrm{pair}}_M(s)+T_M(s)\right)
=-a_3(s)\,\mathrm{Genuine}(s).
}
```

Therefore the complete tail-resolved enriched-pair defect vanishes exactly
at a Genuine zero. At such a zero, the coupled Green ledger equals the
corrected pair boundary plus `Outer + Tail` at every cutoff, and the retained
boundary tends to zero.

The attempted final step is now computed exactly. At a Genuine zero,

```math
\mathrm{CoupledGreen}_{3,M}(s)
\longrightarrow
D_3\!\left(\mathrm{Re}(s)-\frac12\right)\mathcal E_\infty(s),
```

with `E_infinity(s)` nonzero in the open strip. Hence coupled-Green closure at
that zero is equivalent to `Re(s) = 1/2`. Lean also proves that the unscaled
angular correction does not tend to zero at a Genuine zero; its limit is the
negative nonzero reflected pairing. It therefore cannot be reclassified as a
vanishing tail.

This closes the nonlocal defect factorization, but it does not silently turn
that equality into pure Green closure. Lean separately proves

```math
\mathrm{PairBoundary}^{\mathrm{corr}}_M(s)\longrightarrow0
\quad\Longleftrightarrow\quad
\mathrm{Re}(s)=\frac12.
```

Accordingly, the rule that every Genuine zero closes the corrected pair
boundary is kernel-checked to be equivalent to the existing strong
nonvanishing frontier. The distinction between the closed tail-resolved
defect and the still-open pure-Green activation is documented in the
[enriched pair / tail closure audit](docs/ENRICHED_TFVD_PAIR_TAIL_CLOSURE.md).

The central declarations are

```lean
finiteC3CanonicalEnrichedTfvdCorrectedPairBoundary_eq_greenForm
finiteC3CanonicalEnrichedTfvdPairTailReadout_eq_factor_mul_genuine
finiteC3EnrichedTfvdPairTailDefect_eq_neg_tailReadout
finiteC3EnrichedTfvdPairTailDefect_eq_zero_iff_genuine_zero
finiteC3TailResolvedEnrichedTfvdPairIdentity_of_genuine_zero
finiteC3CoupledGreenFlux_sub_correctedPairBoundary_tendsto_zero_of_genuine_zero
finiteC3CoupledGreenFlux_tendsto_radialBulk_of_genuine_zero
finiteCanonicalAngularGreenCorrection_not_tendsto_zero_of_genuine_zero
finiteC3CoupledGreenFlux_tendsto_zero_iff_re_eq_half_of_genuine_zero
c3EnrichedTfvdCorrectedPairBoundaryClosesAt_iff_re_eq_half
genuineZerosCloseC3EnrichedTfvdCorrectedPairBoundary_iff_strongNonvanishing
```

### Pythagorean branch / Green crosswalk

The positional branch defect and the reflected radial Green difference are
not merely zero at the same abscissa. For every prime camera and positive
abscissa, Lean proves the exact signed factorization

```math
b_p(\sigma)
=-\tau_p(\sigma)D_p\!\left(\sigma-\frac12\right),
\qquad
\tau_p(\sigma)
=p^{-(\sigma-1/2)}\left(1-p^{-2\sigma}\right)^{-1}>0.
```

This supplies a canonical positive transfer coefficient between the existing
quadratic carry geometry and the existing radial Green coordinate. Using the
complete enriched-pair tail defect, Lean then forms the real Hilbert vector

```math
\mathcal C_{M,p}(s)=
\left(
  \tau_p\,\mathrm{Re}(D_M^{\mathrm{pair,tail}}),
  \tau_p\,\mathrm{Im}(D_M^{\mathrm{pair,tail}}),
  E_\infty(s)b_p(\mathrm{Re}(s))
\right).
```

Its energy is the exact Pythagorean ledger

```math
\left\lVert\mathcal C_{M,p}(s)\right\rVert^2
=\tau_p^2\,
  \mathrm{normSq}\!\left(D_M^{\mathrm{pair,tail}}(s)\right)
 +\left(E_\infty(s)b_p(\mathrm{Re}(s))\right)^2.
```

The vector is cutoff-invariant. In the open strip its kernel is exactly

```math
\mathcal C_{M,p}(s)=0
\quad\Longleftrightarrow\quad
\mathrm{Genuine}(s)=0
\quad\mathrm{and}\quad
\mathrm{C3Compatible}(\mathrm{Re}(s)).
```

Thus the construction forbids cancellation between the complete Genuine
tail channel and the positional defect channel. It also identifies the
remaining gate without circularity: after the tail/Genuine coordinate has
vanished, vanishing of the completed vector is equivalent to positional
compatibility. The tail zero alone does not annihilate that orthogonal third
coordinate, so no unconditional confinement claim is added.

The exact formulas and scope audit are in the
[branch / Green quadratic crosswalk](docs/BRANCH_GREEN_QUADRATIC_CROSSWALK.md).

The principal declarations are

```lean
branchToGreenTransferCoefficient_pos
branchDefect_eq_neg_transfer_mul_radialDifference
c3EnrichedTailBranchCompletedReadout_norm_sq
c3EnrichedTailBranchCompletedReadout_norm_sq_eq_genuine_branch
c3EnrichedTailBranchCompletedReadout_cutoff_invariant
branchDefectGreenEnergy_sq_le_enrichedTailCompletedReadout_norm_sq
c3EnrichedTailBranchCompletedReadout_eq_zero_iff_genuine_and_compatible
c3EnrichedTailBranchCompletedReadout_eq_zero_iff_compatible_of_tailDefect_zero
```

### Structural carry--TFVD--Green defect principle

The causal order is now packaged as a separate theorem surface. Positional
carry defines the branch defect first. The exact C3 identity then proves that
the differentiated bracket Green form is already the TFVD diagonal, before
any zero or critical-line assumption. Green is therefore a later readout of
the TFVD computation, not the source of the equilibrium.

The defect is also tied directly to this same finite readout:

```math
b_3(\mathrm{Re}(s))P_M(s)
=
-T_3(\mathrm{Re}(s))\,
\mathrm{greenForm}\left(B_M(s),B_M(s^\#)\right).
```

This unconditional identity shows that the structural axis is an exact
positive rescaling of the bracket--TFVD--Green mechanism, not an unrelated
coordinate added afterward.

Define the structural Green-scale energy

```math
\mathcal D_p(s)=
\left(E_\infty(s)b_p(\mathrm{Re}(s))\right)^2.
```

In the open strip, Lean proves

```math
\mathcal D_p(s)=0
\quad\Longleftrightarrow\quad
\mathrm{C3Compatible}(\mathrm{Re}(s))
\quad\Longleftrightarrow\quad
\mathrm{Re}(s)=\frac12,
```

and equivalently

```math
\mathcal D_p(s)>0
\quad\Longleftrightarrow\quad
\mathrm{Re}(s)\ne\frac12.
```

On the half-abscissa, this defect is identically zero for every phase time
without a zero hypothesis. It is the third orthogonal coordinate of the
tail-completed readout, so

```math
\mathcal C_{M,p}(s)=0
\quad\Longrightarrow\quad
\mathcal D_p(s)=0
\quad\Longrightarrow\quad
\mathrm{Re}(s)=\frac12.
```

This is a structural necessity theorem for the completed port: the zero does
not create equilibrium and cannot cancel the prior defect. It does not claim
that the scalar Genuine coordinate alone annihilates this independent third
coordinate.

What scalar vanishing does is now recorded exactly:

```math
\mathrm{Genuine}(s)=0
\quad\Longrightarrow\quad
\left\lVert\mathcal C_{M,p}(s)\right\rVert^2=\mathcal D_p(s).
```

Hence an off-critical scalar zero would leave a strictly positive completed
TFVD norm entirely in the structural leg.

See the
[structural carry--TFVD--Green defect audit](docs/STRUCTURAL_TFVD_GREEN_DEFECT.md).

The principal declarations are

```lean
branchDefect_mul_finiteReflectedGradientPairing_eq_neg_transfer_mul_greenForm
structuralCarryGreenDefectEnergy_eq_zero_iff_compatible
structuralCarryGreenDefectEnergy_criticalLine
structuralCarryGreenDefectEnergy_pos_iff_re_ne_half
structuralCarryGreenDefectEnergy_le_completedReadout_norm_sq
c3EnrichedTailBranchCompletedReadout_norm_sq_of_genuine_zero
c3EnrichedTailBranchCompletedReadout_norm_pos_of_genuine_zero_off_critical
c3EnrichedTailBranchCompletedReadout_eq_zero_iff_re_eq_half_of_genuine_zero
completedReadout_zero_implies_structuralDefect_zero
completedReadout_zero_implies_re_eq_half
genuineBracket_tfvd_green_structuralDefect_capstone
genuineZero_tfvd_completedStructuralResidual_capstone
```

### Canonical-state trace closure

The remaining analytic regularity is now expressed using objects that were
already present in the pinned foundations. Let `m_M(s)` be the canonical
all-prime mass endpoint and let `J_arith` be the closed arithmetic
nonlocal trace. Before any zero is assumed, Lean proves

```math
\mathcal D_p(s)=0
\quad\Longleftrightarrow\quad
m_M(s)\in\mathrm{dom}(J_{\mathrm{arith}}).
```

At a scalar Genuine zero, this becomes an exact characterization of closure
of the three-coordinate completed TFVD port:

```math
\mathcal C_{N,p}(s)=0
\quad\Longleftrightarrow\quad
m_M(s)\in\mathrm{dom}(J_{\mathrm{arith}}).
```

For a multiplicity-one Genuine root, the right-hand side is further
identified with square summability of the material vertical trace of the
canonical global root-tangent mass state already constructed in CPFormal.
Thus the last gate is now a concrete state-specific domain theorem rather
than an unspecified scalar-kernel transport.

This crosswalk does not assert the missing domain membership. Finite TFVD
reconstruction and Pythagorean conservation remain compatible with an
off-domain structural leg; proving that the canonical root-derived trace is
globally square summable is still new analytic work.

See the
[canonical-state trace closure audit](docs/CANONICAL_STATE_TRACE_CLOSURE.md).

The principal declarations are

```lean
structuralCarryGreenDefectEnergy_eq_zero_iff_massState_mem_traceDomain
c3EnrichedTailBranchCompletedReadout_eq_zero_iff_massState_mem_traceDomain
c3EnrichedTailBranchCompletedReadout_norm_pos_iff_massState_not_mem_traceDomain
massState_mem_traceDomain_iff_simpleRoot_globalTraceDomain
c3EnrichedTailBranchCompletedReadout_eq_zero_iff_simpleRoot_globalTraceDomain
simpleGenuineRoot_completedPort_traceClosure_capstone
```

## Exact radial factorization and the remaining frontier

The bracket-resolved boundary form admits the expected finite radial
factorization. Write

```math
\delta=\mathrm{Re}(s)-\frac12,
\qquad
D_3(\delta)=3^\delta-3^{-\delta}.
```

Then Lean proves, for every cutoff `M` and every complex parameter `s`,

```math
\boxed{
\mathrm{greenForm}
\left(B_M^{\mathrm G}(s),B_M^{\mathrm G}(s^\#)\right)
=D_3(\delta)\,\mathcal E_M^\#(s)
}.
```

This factorization is unconditional: it mentions neither zeros nor the
critical strip. Inside the open Genuine strip, the finite reflected pairing
converges to a nonzero limit. Consequently, the concrete bracket-resolved
Green form closes in the limit exactly when

```math
\mathrm{Re}(s)=\frac12.
```

The scalar Genuine zero identity has a different, equally exact consequence.
At a Genuine zero it proves

```math
\mathrm{greenForm}
\left(B_{3M}^{\mathrm G}(s),B_{3M}^{\mathrm G}(s^\#)\right)
+D_3(\delta)\,\mathrm{Correction}_M(s)
\longrightarrow 0.
```

Here the correction is not a vanishing remainder: its limit is the negative
of the infinite reflected pairing. Thus the scalar zero cancels the Green
channel against its retained provenance channel; it does not, by itself,
annihilate the Green channel separately. The global assertion that every
Genuine zero closes this Green form is proved equivalent to the existing
strong nonvanishing statement in the strip. This records the exact
confinement frontier instead of assuming it inside the factorization.

The public theorems are

```lean
greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_radialFactorization
greenForm_finiteC3GenuineBracketGreenBoundaryPair_tendsto
greenForm_finiteC3GenuineBracketGreenBoundaryPair_tendsto_zero_iff
genuineZero_greenForm_add_scaledAngularCorrection_tendsto_zero
genuineZeros_closeC3GenuineBracketGreenForm_iff_strongNonvanishing
```

## Reflected Green form crosswalk

The package also compares the reflected CP Green flux with the abstract
boundary form from `native-carry-spectral-weyl`. For the canonical camera
`p = 3` and cutoff `M`, it keeps every arithmetic cell as an orthogonal
coordinate in

```math
H_M=\ell^2(\{0,\ldots,M-1\};\mathbb C)
```

and forms the direct boundary pair

```math
B_M(s)=
\left(
  \bigl(\widetilde\nabla_3(s,n)\bigr)_{n<M},
  \bigl(\nabla^+(s,n)\bigr)_{n<M}
\right).
```

Lean proves the exact identity

```math
\mathrm{greenForm}\bigl(B_M(s),B_M(s^\#)\bigr)
=\mathcal W^{\mathrm{CP}}_{3,M}(s).
```

This is a literal identification of forms, not an analogy between two objects
called Green. It has no zero or critical-line hypothesis. As a concrete
consequence, if the two boundary pairs belong to one Green-isotropic relation,
then the reflected C3 flux vanishes. The public theorems are

```lean
greenForm_finiteC3GreenBoundaryPair_eq_orientedFlux
finiteOrientedC3GreenFlux_eq_zero_of_isotropicBoundary
finiteOrientedC3GreenFlux_eq_zero_of_maximalIsotropicBoundary
bracketCoupledC3GreenFlux_tendsto_zero_of_genuineZero_and_isotropy
re_eq_half_of_genuineZero_and_isotropicC3Boundary
```

The arithmetic membership statement remains explicit: this module does not
claim that scalar Genuine closure by itself places `B_M(s)` and `B_M(s#)` in
the relation. That membership/intertwining is the remaining boundary
transport, rather than another identity between the two Green forms. Once
that concrete membership is supplied at every cutoff, Lean composes it with
the existing Genuine boundary telescoping and reflected-energy positivity to
obtain

```math
\mathrm{Re}(s)=\frac12.
```

## Minimal-provenance carrier

The repository now constructs the finite enriched carrier instead of choosing
an inverse of scalar synthesis. Let `Q_M` sum the preserved cells in each of
the two Green legs and let `A_M` retain the complete cellwise port. The
canonical carrier is

```math
\widehat H_M=
H_M\big/\bigl(\ker Q_M\cap\ker A_M\bigr).
```

Lean proves

```math
\ker Q_M\cap\ker A_M=\{0\},
\qquad
\widehat H_M\simeq H_M,
```

and proves that the joint scalar/provenance range is a closed
finite-dimensional relation. Thus retaining the reflected Green form forces
the finite port to keep every arithmetic cell; no section, pseudoinverse, or
preferred representative is involved. Reading the analysis leg of the
enriched class recovers `B_M(s)` exactly, and its Green form remains the
oriented CP flux.

The fixed diagonal Green relation provides an exact audit of the last
membership law. In the open Genuine strip, Lean proves

```math
\left[
  \forall M,\;
  B_M(s),B_M(s^\#)\text{ belong to the diagonal Green relation}
\right]
\quad\Longleftrightarrow\quad
\mathrm{Re}(s)=\frac12.
```

Consequently, requiring this transport at every Genuine zero is equivalent to
the existing `GenuineStrongNonvanishingInStrip` frontier. The carrier and its
closedness are therefore complete; scalar Genuine vanishing still does not,
by itself, prove the diagonal membership. This equivalence prevents the
remaining confinement statement from being hidden inside the carrier
definition.

## Exact finite identity

For every real phase time `t`, natural camera `b`, and finite cutoff `M`, Lean
proves

```math
\mathrm{pack}\bigl(N_{b,M}(t)\bigr)
=\chi_{b,M}\left(\frac12+it\right).
```

Here `pack` stores the two real coordinates in the real and imaginary fields
of a complex number. It is an injective additive map; it does not change the
operator.

The public theorem is

```lean
theorem packaged_finiteNativeOperator_eq_finiteBracketCharacteristic
    (time : ℝ) (camera cutoff : ℕ) :
    nativeCarryRealPlaneComplexPackaging
        (Operator.finiteNativeOperator camera cutoff time) =
      finiteBracketCharacteristic camera cutoff (nativeLine time)
```

The proof factors through the common free integer stencil:

```text
FormalStencil ── evalStencil(time) ──→ RealPlane
      │                                  │ packaging
      │                                  ▼
      └── evalDirichletStencil ────────→ Complex
```

Both upstream evaluation theorems were already kernel-checked. This package
proves that packaging commutes with evaluation of every formal stencil and
then specializes the commuting square to `finiteStencil camera cutoff`.

Because the theorem is stencil-level, it covers all natural cameras,
including the exceptional C2 convention and the final endpoint correction of
even cameras.

## Exact consequences

Finite vanishing is preserved in both directions:

```math
N_{b,M}(t)=0
\quad\Longleftrightarrow\quad
\chi_{b,M}\left(\frac12+it\right)=0.
```

The visible quadratic energies are also identical:

```math
\mathrm{normSq}\!\left(
  \chi_{b,M}\left(\frac12+it\right)
\right)
=\left\|N_{b,M}(t)\right\|_{\mathbb R^2}^{2}.
```

These are finite algebraic identities. By themselves they do not assert
convergence of the C3 corrected residual, existence of a limiting zero, or
confinement of any infinite zero set.

## Explicit C3 boundary jet

For positive real `x`, the package defines the recurrent coefficients

```math
c_0(s)=1,
\qquad
c_{r+1}(s)=c_r(s)(-s-r),
```

and the closed spatial derivatives

```math
D^r_x\left(x^{-s}\right)=c_r(s)x^{-s-r}.
```

Lean checks the complex-power derivative rule at arbitrary order and proves
that the next recurrent closed form is exactly its derivative value. The C3
boundary point is the literal ledger convention

```math
C_M=3(M+1),
```

and the oriented fifth-order jet is

```math
J_M(s)
=-\frac{F_s'(C_M)}{3}
+\frac{F_s''(C_M)}{2}
-\frac{5F_s'''(C_M)}{18}
+\frac{F_s''''(C_M)}{24}
+\frac{F_s'''''(C_M)}{60},
\qquad
F_s(x)=x^{-s}.
```

No generic placeholder is used for `J_M`: every derivative and every rational
coefficient above occurs in `c3OrientedBoundaryJet`.

The corrected residual is then defined in real coordinates by

```math
A_M(t)=N_{3,M}(t)+\mathrm{unpack}\left(J_M\left(\frac12+it\right)\right),
```

and in complex coordinates by

```math
\widetilde A_M(t)
=\chi_{3,M}\left(\frac12+it\right)
+J_M\left(\frac12+it\right).
```

Lean proves the exact commuting identity

```math
\mathrm{pack}\bigl(A_M(t)\bigr)=\widetilde A_M(t)
```

and the exact quadratic-energy identity

```math
\mathrm{normSq}\bigl(\widetilde A_M(t)\bigr)
=\left\|A_M(t)\right\|_{\mathbb R^2}^{2}.
```

## Corrected velocity and stationary equation

The first time derivative of the boundary correction is not introduced as an
independent placeholder. Lean differentiates the recurrent coefficients and
the complex power kernel, proves the resulting exponent derivative, and then
composes it with the native line. Thus

```math
J_M^{(1)}(t)
=\frac{d}{dt}J_M\left(\frac12+it\right)
```

is a kernel-checked identity. The corrected complex velocity is

```math
\widetilde B_M(t)
=\frac{d}{dt}\chi_{3,M}\left(\frac12+it\right)+J_M^{(1)}(t),
```

and its real two-coordinate presentation is

```math
B_M(t)=\mathrm{unpack}\bigl(\widetilde B_M(t)\bigr).
```

Lean proves both derivative statements

```math
\frac{d}{dt}\widetilde A_M(t)=\widetilde B_M(t),
\qquad
\frac{d}{dt}A_M(t)=B_M(t).
```

The corrected stationary numerator and energy are defined by

```math
h_M(t)=A_M(t)\mathbin{\cdot}B_M(t),
\qquad
E_M(t)=\left\|A_M(t)\right\|_{\mathbb R^2}^{2}.
```

Their exact differential relation is

```math
E_M'(t)=2h_M(t).
```

Lean also differentiates the velocity exactly:

```math
A_M^{(2)}(t)=B_M'(t).
```

The stationary slope is the explicit identity

```math
h_M'(t)
=B_M(t)\mathbin{\cdot}B_M(t)
 +A_M(t)\mathbin{\cdot}A_M^{(2)}(t).
```

Thus neither the slope nor the acceleration is supplied by numerical
differentiation.

Consequently, the Lean predicate `IsC3CorrectedStationaryCenter M t`, defined
by `h_M(t) = 0`, is equivalent to `E_M'(t) = 0`. No decimal approximation is
used to define a center.

There is also an exact oriented test. At a stationary time with nonzero
velocity,

```math
A_M(t)=0
\quad\Longleftrightarrow\quad
\det\bigl(A_M(t),B_M(t)\bigr)=0.
```

This is a finite-dimensional consequence of orthogonality and the oriented
determinant; it does not assert that a stationary center exists.

## Uniform stationary-root promotion

The stationary-localization ledger fixes the exact cutoff threshold

```math
M_0=131072
```

and the exact rational anchor interval

```math
I=
[92.491899270558483805857220904387963299360620986373,
 92.491899270558484805857220904387963299360620986373].
```

The kernel-facing structure `C3StationaryIntervalCertificate` asks for the
three concrete enclosure facts that the localization argument needs:

1. `h_M` is negative at the left endpoint for every `M ≥ M₀`;
2. `h_M` is positive at the right endpoint for every `M ≥ M₀`;
3. `h_M'` is positive throughout the open interval for every `M ≥ M₀`.

From exactly these facts, Lean proves

```math
\forall M\ge M_0,\qquad
\exists!c_M\in I,\quad h_M(c_M)=0.
```

It then selects `correctedStationaryCenter certificate M`, proves that it is
the unique stationary point in `I`, and defines the precise ledger sequence

```math
Q_M=
\left\lVert A_M
  (\mathrm{correctedStationaryCenter}(\mathrm{certificate},M))
\right\rVert.
```

No floating-point center enters this definition. Below `M₀` the selector has
an explicitly documented default value, and no theorem calls that default a
stationary point.

The module `C3StationaryLedgerBridge` now reifies the actual limiting-chart
architecture used by the ledger. It defines the concrete infinite C3
residual, velocity, acceleration, stationary numerator `H∞`, and stationary
slope. It also fixes conservative rational bounds implied by the Arb output:

```math
\begin{aligned}
H_\infty(a)&\le-9\times10^{-15},
&9\times10^{-15}&\le H_\infty(b),\\
21&\le S_\infty(t),
&|h_M-H_\infty|&\le10^{-15},\\
&&|h_M'-S_\infty|&\le10^{-12}.
\end{aligned}
```

Here `S∞` is the limiting product-rule expression formed from the limiting
residual, velocity, and acceleration.

Lean verifies the rational margin comparisons and proves that these five
sound enclosures produce `C3StationaryIntervalCertificate`, hence the unique
root family. This closes all of the ledger's order arithmetic and logical
transport in the kernel.

An inhabitant of `C3StationaryLedgerEnclosures` has **not** yet been proved in
Lean. Its remaining fields are precisely the transcendental interval leaves
currently evaluated by Arb: limiting endpoint values, limiting slope on the
anchor interval, and corrected finite-to-limit perturbations. No Arb ball is
silently promoted to a theorem.

After that explicit bridge is closed, the next analytic obligation is proving
`Q_M → 0`; neither the enclosure interface nor the root-selection theorem
assumes this limit.

## Prime-to-all-bases camera form bridge

The native real plane and its complex notation remain literally the same
two-coordinate readout after all-bases completion. Lean proves

```math
\mathrm{extend}\!\left(\mathrm{pack}\circ q\right)
=
\mathrm{pack}\circ\mathrm{extend}(q),
```

so packaging preserves both zeros and quadratic energy after completion.

Finite prime-camera coefficients embed injectively into `CameraFinsupp`. The
selected prime carrier inherits the intrinsic all-bases Gram norm. Every
bounded scalar functional on this carrier extends to `CameraHilbert` with the
same norm. The same theorem is proved for a native real-plane readout by
extending its two real coordinates and reassembling the pair:

```math
\widehat q\!\left(\mathrm{cameraEmbedding}(\iota_{\mathbb P}u)\right)
=q(u),
\qquad
\lVert\widehat q\rVert=\lVert q\rVert.
```

Lean also computes, for every odd prime,

```math
\lVert v_p\rVert^2=p(p-1),
```

and proves that no bounded map can send the norm-one axes of the raw
unweighted prime Hilbert space to these camera vectors. Therefore the missing
research estimate must be stated in the intrinsic Gram norm. The actual
enriched Green/Haar core formula and its uniform Gram bound remain the next
analytic gate; this bridge asserts no zero-to-Green implication and no global
confinement theorem.

See the
[prime-to-all-bases camera form audit](docs/PRIME_ALL_BASES_CAMERA_FORM.md).

The principal new declarations are

```lean
extend_packageRealPlaneCameraCoreMap
packageRealPlane_extended_eq_zero_iff
normSq_packageRealPlane_extended_eq_realEnergy
primeCameraCoreReindex_injective
extendPrimeCameraGramCoreToHilbert_norm
extendPrimeCameraGramCoreRealPlaneToHilbert_apply
extendPrimeCameraGramCoreRealPlaneToHilbert_norm
gramKernel_primeCameraIndex_self
norm_cameraVector_prime_sq
no_bounded_rawPrimeCameraAxis_synthesis
```

## Full endpoint and exact Poisson return

The normalized Green-frame endpoint reconstructs its bulk exactly through
the existing Poisson operator:

```math
E x=0
\Longrightarrow
M(E x)=B x=0.
```

When the bulk norm realizes the structural carry--Green defect, Lean then
derives zero defect and `Re(s) = 1/2`. The finite C3 full port has the exact
factorization

```math
\mathrm{Bulk}_{M}(s)
=
\mathrm{RadialDifference}_3(s)\,
\mathrm{ReflectedPairing}_{M}(s).
```

The endpoint must not be confused with its scalar synthesis. At a Genuine
zero the tail-completed scalar readout is zero, while the canonical complete
Green port remains nonzero at every nonempty cutoff. Thus the remaining
activation condition is Green isotropy of the complete direct/reflected
ports, not vanishing of the endpoint itself.

See the [full-endpoint audit](docs/FULL_ENDPOINT_POISSON_DEFECT.md).

## Universal linear-kernel guardrail

On the minimal joint carrier retaining both coarse synthesis and full Green
provenance, Lean proves

```math
\ker(\mathrm{stateReadout})
\not\subseteq
\ker(\mathrm{GreenBulk}).
```

The same obstruction has a witness inside the universal enriched TFVD
transport with seed `1` and a complete block. This does not refute a theorem
specific to the canonical Dirichlet curve; it proves that such a theorem
must use the global one-parameter coherence of that curve and cannot follow
from a universal linear carrier alone.

See the
[arithmetic linear-kernel audit](docs/ARITHMETIC_LINEAR_KERNEL_AUDIT.md).

## Completed TFVD ledger and faithful C3--Naimark lift

The canonical same-edge completed residual is now audited exactly. Lean proves
that it is always a real scalar multiple of one fixed tower generator, so
every linear realization of the residual-only family has rank at most one.
The lossless source therefore retains the ordinary TFVD state, logarithmic
jet, and precompression residual as separate ledger entries.

Independently, one complete C3 block, with three arithmetic cells on each
Green leg, is packed faithfully into six all-bases camera labels. The port has
six complex coordinate slots (twelve real slots after realification); this is
the dimension of the ambient carrier, not a claim that the canonical parameter
curve fills it. The bounded packing and its Naimark promotion are injective,
canonical adjoint compression recovers the packed state exactly, and the
coordinatewise Naimark isometry preserves the realified Green skew form.

This constructs the faithful carrier and proves the residual-only rank
obstruction. It does not identify the completed residual scalar with the C3
Green form or manufacture an inverse from the collapsed residual.

See the
[completed TFVD--Naimark feasibility audit](docs/COMPLETED_TFVD_NAIMARK_FEASIBILITY.md).

## Pinned foundations

| Package | Revision |
|---|---|
| `CarryGeometry` | `1f85b8c3ab5ded27a0782956e1ada0dd8a1b6fd4` (`v0.1.0`) |
| `CPFormal` | `65d50f6db1208708e109982ba97e1d51d3039956` (`v0.62.0-1-g65d50f6`) |
| `NativeCarrySpectralWeyl` | `298d83c9351e308a5213b9f5ac32e44087f98a9f` (form-first extension) |
| `FiniteNativeCarryOperator` | `00e9d6beb17226545abf5ddf90bbfede6c7146b0` (`v0.1.0`, transitive pin) |
| `GreenFrame` | `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa` (`v2.1.0`, transitive pin) |
| Lean / Mathlib | `v4.32.0` |

## Audit

Run the complete local audit with:

```bash
bash scripts/audit.sh
```

The audit builds with warnings as errors, rejects local trust escapes, checks
publication metadata and GitHub Markdown, and evaluates `#print axioms` for
every public theorem. The dependency allowlist is restricted to `propext`,
`Classical.choice`, and `Quot.sound`.

Versioned releases carry `CITATION.cff` and `.zenodo.json` metadata. Release
`v0.1.0` remains preserved by Zenodo under the version DOI
[`10.5281/zenodo.21935706`](https://doi.org/10.5281/zenodo.21935706). The
concept DOI
[`10.5281/zenodo.21935705`](https://doi.org/10.5281/zenodo.21935705) resolves
to the latest archived version of this repository, including `v0.3.0` after
the GitHub release is ingested.
