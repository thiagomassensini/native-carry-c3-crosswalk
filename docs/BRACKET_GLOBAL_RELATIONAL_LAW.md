# Global relational law of the bracket

This checkpoint names the invariant shared by the native real operator,
analytic bracket characteristic, differentiated Genuine bracket, enriched
TFVD diagonal, Green boundary form, and closed arithmetic trace.

## One finite computation in several presentations

For every finite cutoff and every complex parameter, the existing crosswalks
identify the resolved bracket boundary form with both the oriented Genuine
flux and the TFVD diagonal. The same form has the exact factorization

~~~math
B_M(s)
=
\Delta_3\!\left(\operatorname{Re}(s)-\frac12\right)
P_M(s).
~~~

The new theorem

~~~lean
finiteNativeGenuineTfvdGreenBracketLaw
~~~

packages these equalities together with the existing native-real/complex
coordinate identity. It introduces no zero, strip, limit, or equilibrium
hypothesis.

## Two readouts of the bracket

The scalar bracket chart and the differentiated Green bracket are related but
must not be conflated.

Inside the open Genuine strip,

~~~math
\operatorname{Chart}_3(s)
=
a_3(s)\operatorname{Genuine}(s),
\qquad a_3(s)\ne0.
~~~

Hence a Genuine zero annihilates the scalar bracket value. Lean records this
as

~~~lean
genuineZero_scalarBracketChart_eq_zero
~~~

The differentiated Green bracket instead satisfies

~~~math
B_\infty(s)=0
\quad\Longleftrightarrow\quad
\operatorname{Re}(s)=\frac12,
~~~

because the limiting reflected pairing is nonzero. This is exposed through

~~~lean
C3GenuineBracketGreenClosesAt
c3GenuineBracketGreenClosesAt_iff_re_eq_half
~~~

A zero of a scalar function does not in general annihilate its differentiated
boundary form. Keeping those two coordinates separate is what prevents the
global statement from being inserted circularly.

## Operator-domain form

The arithmetic nonlocal trace is a closed self-adjoint partial operator. Its
graph is a fixed maximal Green-isotropic relation. For the canonical mass
state, Lean proves the pointwise law

~~~math
\Psi_s\in\mathcal D(J_{\mathrm{arith}})
\quad\Longleftrightarrow\quad
B_\infty(s)=0
\quad\Longleftrightarrow\quad
\operatorname{Re}(s)=\frac12.
~~~

The first equivalence is

~~~lean
primeMassGreenBulkState_mem_traceDomain_iff_c3GenuineBracketGreenClosesAt
~~~

and admissibility yields both graph membership and concrete bracket closure:

~~~lean
canonicalMassTraceDomain_realizesBracketLaw
~~~

The positive structural carry--Green energy has the same zero locus:

~~~lean
structuralCarryGreenDefectEnergy_eq_zero_iff_c3GenuineBracketGreenClosesAt
~~~

Thus the bracket, the operator domain, the maximal Green-isotropic graph, the
positive structural defect, and the positional tilt are exact presentations
of one pointwise condition.

## Law at a zero

At a Genuine zero, Lean now packages the exact distinction:

~~~math
\operatorname{Chart}_3(s)=0,
~~~

while

~~~math
\Psi_s\in\mathcal D(J_{\mathrm{arith}})
\quad\Longleftrightarrow\quad
B_\infty(s)=0
\quad\Longleftrightarrow\quad
\operatorname{Re}(s)=\frac12.
~~~

The declaration is

~~~lean
genuineZero_bracketRelationalLaw
~~~

It does not infer the second line from the first. It states precisely which
kernel-reflecting relation must be activated.

## Global law

The two global activation predicates are:

~~~lean
GenuineZerosLieInArithmeticNonlocalTraceDomain
GenuineZerosCloseC3GenuineBracketGreenForm
~~~

Lean proves

~~~math
\begin{aligned}
&\text{every Genuine zero supplies a trace-domain state}\\
{}\Longleftrightarrow{}&
\text{every Genuine zero closes the Green bracket}\\
{}\Longleftrightarrow{}&
\text{GenuineStrongNonvanishingInStrip}.
\end{aligned}
~~~

The public capstones are

~~~lean
genuineZerosLieInTraceDomain_iff_closeC3GenuineBracketGreenForm
genuineZerosCloseC3GenuineBracketGreenForm_iff_strongNonvanishing
genuineBracket_global_relational_capstone
~~~

This is a global theorem about the relation between the objects rather than
an extra property attached to one presentation.

## Exact scope

The module closes the crosswalk and proves the equivalence law. It does not
assert unconditionally that every Genuine zero belongs to the trace domain or
that every such zero closes the differentiated Green bracket. Proving that
activation from an independent height/Weyl realization would immediately
feed the established capstone; assuming it here would merely rename the
global confinement statement.
