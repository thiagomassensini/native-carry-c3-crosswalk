# Arithmetic nonlocal trace audit

This note records the exact result of the search for an arithmetic trace from
the Genuine/CP carrier to a fixed Green-isotropic boundary relation. The
construction is structural and valid before any zero is considered. It does
not prove a global confinement statement.

## Existing types and selected carrier

The finite C3 layer already has these types:

~~~lean
FiniteC3GreenBoundarySpace M
FiniteC3GreenPortCarrier M
FiniteC3MinimalProvenanceCarrier M
~~~

The canonical equivalence

~~~lean
finiteC3MinimalProvenanceEquivPort M :
  FiniteC3MinimalProvenanceCarrier M ≃ₗ[ℂ]
    FiniteC3GreenPortCarrier M
~~~

shows that preserving coarse synthesis and full Green analysis leaves no
finite direction to quotient out. The joint kernel is trivial.

The global prime-camera layer already supplies two completed carriers:

~~~lean
PrimeGreenCameraHilbert := lp (fun _ : Nat.Primes => ℝ) 2
PrimeCarryVerticalHilbert := lp (fun _ : Nat.Primes => CarryVerticalL2) 2
~~~

The first is the smallest existing Hilbert carrier containing the
mass-normalized prime profile throughout the open strip. It was selected as
the domain and codomain of the nonlocal amplitude trace:

~~~lean
ArithmeticMassCarrier := PrimeGreenCameraHilbert
ArithmeticEnrichedBoundaryPort :=
  ArithmeticMassCarrier × ArithmeticMassCarrier
~~~

No new Green operator is introduced. The relation uses the existing Spectral
Weyl type:

~~~lean
GreenRelation ℝ ArithmeticMassCarrier
~~~

## Canonical closed trace

For a prime camera, let the damping weight be the first carry amplitude:

~~~math
q_p=p^{-1/2}.
~~~

Lean constructs the bounded injective map

~~~math
R(v)_p=q_pv_p
~~~

on the completed mass carrier. Its range is dense. The arithmetic nonlocal
trace is defined without a selected inverse or pseudoinverse:

~~~lean
arithmeticNonlocalTrace := arithmeticPrimeDampingPMap.inverse
~~~

Its exact domain is

~~~math
\mathcal D(J_{\mathrm{arith}})=
\left\{v\in\ell^2(\mathbb P;\mathbb R):
  \sum_{p\in\mathbb P}|q_p^{-1}v_p|^2<\infty
\right\}.
~~~

On that maximal domain, Lean proves

~~~math
(J_{\mathrm{arith}}v)_p=q_p^{-1}v_p=\sqrt p\,v_p.
~~~

The operator is densely defined, closed, closable, symmetric, and
self-adjoint. Consequently its graph

~~~math
\mathcal L_{\mathrm{arith}}
=\left\{(v,J_{\mathrm{arith}}v):
  v\in\mathcal D(J_{\mathrm{arith}})\right\}
~~~

is a closed maximal Green-isotropic relation.

The enriched port preserves both legs:

~~~lean
arithmeticNonlocalBoundaryPort mass =
  (mass, arithmeticNonlocalTrace mass)
~~~

and the concrete boundary defect is

~~~math
D_{\partial}(v,w)=w-J_{\mathrm{arith}}v.
~~~

Lean proves, for every port in the defect domain,

~~~math
D_{\partial}(v,w)=0
\quad\Longleftrightarrow\quad
(v,w)\in\mathcal L_{\mathrm{arith}},
~~~

and, for every input in the trace domain,

~~~math
D_{\partial}\left(v,J_{\mathrm{arith}}v\right)=0.
~~~

These statements use no spectral parameter, zero predicate, critical-line
hypothesis, or tilt hypothesis.

## Unconditional bracket--TFVD--Green intertwining

At every finite prime atlas, every cutoff, and every complex parameter, the
output leg of the finite arithmetic port is literally the existing enriched
log-jet Green state. Coordinatewise, Lean proves

~~~math
\mathrm{EnrichedBracketGreenReadout}_{p,M}(s)
=\mathrm{VerticalTraceFlux}_{p,3M}(s).
~~~

Equivalently, the mass-normalized endpoint is multiplied by the inverse carry
amplitude and becomes the critical-amplitude Green profile. This is the
unconditional structural identity supplied by the existing Genuine-bracket,
TFVD, provenance, and vertical-trace modules. Lean also proves that every
finite port belongs literally to the fixed maximal Green-isotropic graph; no
zero or half-abscissa hypothesis is needed at finite support.

## The first impossible universal step

The requested everywhere-defined Hilbert map does not exist on the current
completed carrier. Lean proves the stronger theorem
no_everywhere_globalPrimeVerticalTrace without assuming linearity or
continuity of the proposed map.

The explicit witness is a global vertical state with first-level mass
p⁻¹ in every prime camera. Its state and centered bracket are
square-summable, but its material trace flux is p⁻¹/². The squared
profile is 1/p, which is not summable over the primes. Therefore no function
into PrimeGreenCameraHilbert can return all of those trace coordinates.

There is also a finite obstruction to factoring a relation-detecting defect
through coarse Genuine synthesis alone. At cutoff two, the explicit vector

~~~math
x=((1,-1),0)
~~~

satisfies

~~~math
Qx=0,
\qquad
x\notin\mathcal L_{\mathrm{diag}}.
~~~

Lean proves that no linear maps boundaryDefect and transport can satisfy both

~~~math
\mathrm{boundaryDefect}
=\mathrm{transport}\circ Q
~~~

and

~~~math
\mathrm{boundaryDefect}(x)=0
\quad\Longleftrightarrow\quad
x\in\mathcal L_{\mathrm{diag}}.
~~~

Thus a pair of synthesized finite scalars cannot characterize the fixed
isotropic relation. The map must retain provenance plus a genuinely nonlocal
endpoint or tail.

## Exact remaining gate

For the canonical mass state in the open strip, Lean proves

~~~math
\mathrm{primeMassGreenBulkState}(M,s)
\in\mathcal D(J_{\mathrm{arith}})
\quad\Longleftrightarrow\quad
\mathrm{criticalDisplacement}(\mathrm{Re}(s))=0.
~~~

When this domain membership is available, the trace recovers the complete
critical-amplitude Green profile coordinatewise. But asking every Genuine
zero to supply that membership is proved equivalent to
GenuineStrongNonvanishingInStrip:

~~~lean
genuineZero_to_arithmeticNonlocalTrace_domain_iff_strongNonvanishing
~~~

It is therefore not a permissible intermediate lemma in a noncircular proof
of the same confinement statement.

The current exact diagram is

~~~text
mass-normalized Genuine/CP profile
              |
              | J_arith (closed, partial)
              v
critical-amplitude Green profile
              |
              v
fixed maximal Green-isotropic graph
~~~

The first arrow is defined precisely on its maximal domain. What remains is
an independent arithmetic regularity theorem placing the relevant state in
that domain, or a new rigged codomain together with a separately proved
synthesis into the Spectral Weyl boundary space. PoissonCompletion retains
endpoint and bulk, SourceRelation turns a supplied port into a maximal
isotropic relation, and the Hatano result compresses an already factored
defect; none constructs the missing half-amplitude regularity.

## Type boundary with the other repositories

The Spectral Weyl source relation uses a supplied map into its all-bases
camera completion. The Green Frame Poisson completion lands in its own
external/bulk Hilbert sum. The current arithmetic trace lands in
PrimeGreenCameraHilbert. No existing continuous linear map identifies these
three completed spaces.

This is why the construction uses the common GreenRelation API but does not
claim that it is already the concrete carryWeylBoundaryGraph. Such a claim
would require a new bounded or rigged synthesis theorem, including its
endpoint/return preservation law.

## What follows if the gate is closed independently

No new radial argument is needed after independent domain membership and a
proved boundary identification. The existing theorem

~~~lean
greenForm_finiteC3GenuineBracketGreenBoundaryPair_tendsto_zero_iff
~~~

states in the open strip that closure of the concrete bracket-resolved Green
form is equivalent to Re(s) = 1/2. This implication was checked only as a
downstream dependency; it was not used to construct the trace.
