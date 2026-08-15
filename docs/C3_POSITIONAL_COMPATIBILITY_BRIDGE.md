# C3 zero and foundational positional compatibility

This bridge imports the frozen `carry-geometry` foundation and tests the
three-lemma decomposition directly against the native C3 zero predicate.

## Lemma 1: compatibility without the half-abscissa

The new integration predicate is only an alias of the foundational notion:

~~~math
\mathrm{C3Compatible}(\sigma)
\quad:=\quad
\forall k>0,\qquad
\left(3^{-k\sigma}\right)^2=3^{-k}.
~~~

Its Lean name is `C3PositionalGeometryCompatible`. The definition does not
mention `1/2`, an operator, a zero, a prime, Green geometry, or Genuine.

## Lemma 2: purely geometric rigidity

The foundational theorem from `carry-geometry` gives immediately

~~~math
\mathrm{C3Compatible}(\sigma)
\quad\Longleftrightarrow\quad
\sigma=\frac12.
~~~

The integration layer also proves that this minimal predicate is equivalent
to the independently defined native real-plane mass compatibility:

~~~math
\mathrm{C3Compatible}(\sigma)
\quad\Longleftrightarrow\quad
\mathrm{NativeRealMassCompatible}(\sigma,t).
~~~

The phase `t` is arbitrary. Both sides select the same exponent by separate
quadratic calculations.

## Lemma 3: the attempted zero transport

The exact desired statement on the open strip is

~~~math
\mathrm{IsNativeC3Zero}(\sigma,t)
\quad\Longrightarrow\quad
\mathrm{C3Compatible}(\sigma).
~~~

It is packaged as
`C3OperatorZerosPreservePositionalGeometryInStrip`. This proposition also
does not mention `1/2`.

The existing libraries do not supply an inhabitant of this proposition.
Instead, Lean reduces it exactly in three independent ways:

~~~math
\begin{aligned}
&\mathrm{C3ZerosPreserveGeometry}\\
&\quad\Longleftrightarrow
\mathrm{BoundaryClosurePreservesMass}\\
&\quad\Longleftrightarrow
\mathrm{NativeRealPlaneZeroRigidity}\\
&\quad\Longleftrightarrow
\mathrm{GenuineStrongNonvanishingInStrip}.
\end{aligned}
~~~

Pointwise, after using the already-proved identity between the C3 native and
Genuine zero predicates, Lean obtains exactly

~~~math
\left[
\mathrm{IsNativeC3Zero}(s)
\Longrightarrow
\mathrm{C3Compatible}(\mathrm{Re}(s))
\right]
\quad\Longleftrightarrow\quad
\left[
\mathrm{Genuine}(s)=0
\Longrightarrow
\mathrm{Re}(s)=\frac12
\right].
~~~

Therefore the three-lemma decomposition is correct and minimal, but the
third lemma does not follow from the first two. It is precisely the remaining
scalar-zero to quadratic-geometry transport. Calling it “compatibility” makes
its causal meaning clearer; it does not reduce its logical strength.

## Conditional capstone

The final theorem is deliberately conditional:

~~~math
\mathrm{C3ZerosPreserveGeometry}
\Longrightarrow
\left[
  \mathrm{IsNativeC3Zero}(\sigma,t)
  \Longrightarrow
  \mathrm{C3Compatible}(\sigma)
  \mathbin{\land}
  \sigma=\frac12
\right].
~~~

This capstone is short because all geometry is already in the foundation. It
does not claim that the transport premise has been proved.

## Public Lean declarations

~~~lean
C3PositionalGeometryCompatible
c3PositionalGeometryCompatible_iff
c3PositionalGeometryCompatible_iff_nativeRealPlaneMassCompatible
C3OperatorZerosPreservePositionalGeometryInStrip
c3OperatorZero_implies_positionalCompatibility_iff_pointwise_zeroRigidity
c3OperatorZerosPreservePositionalGeometryInStrip_iff_boundaryClosurePreservesMass
c3OperatorZerosPreservePositionalGeometryInStrip_iff_nativeZeroRigidity
c3OperatorZerosPreservePositionalGeometryInStrip_iff_strongNonvanishing
c3OperatorZero_positionalCompatibility_capstone
~~~

The implementation is in
[`C3PositionalCompatibilityBridge.lean`](../NativeCarryC3Crosswalk/C3PositionalCompatibilityBridge.lean).
