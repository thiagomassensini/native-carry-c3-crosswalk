# Genuine control of the existing carry energy

This audit tests the noncompensation route without defining another norm. The
energy is the prime-camera Hilbert norm already constructed in `CPFormal`.

## The coercive leg is complete

For a nonempty cutoff `M` and one prime camera `p`, set

~~~math
E_{M,p}(s)=
\left\lVert
  \mathrm{primeGreenBulkFiniteState}(M,s,\{p\})
\right\rVert^2.
~~~

Lean proves, for every `s` in the open Genuine strip,

~~~math
E_{M,p}(s)=0
\quad\Longleftrightarrow\quad
\mathrm{branchDefect}(p,\mathrm{Re}(s))=0
\quad\Longleftrightarrow\quad
\mathrm{Re}(s)=\frac12.
~~~

This result uses the existing exact factorization

~~~math
\mathrm{profile}_{M,p}(s)
=p^{-1/2}
 \bigl(p^{\delta}-p^{-\delta}\bigr)
 \mathrm{Re}\,\mathcal E_M(s),
\qquad
\delta=\mathrm{Re}(s)-\frac12,
~~~

where the finite reflected energy has strictly positive real part. Thus a
single camera already sees the same unique zero as `branchNormSq - 1`. The
all-prime atlas is not needed for this zero-locus statement.

## The direct upper-control target

The most direct coefficient-one estimate is

~~~math
E_{M,p}(s)
\le
\mathrm{normSq}\!left(a_3(s)\,\mathrm{Genuine}(s)\right),
~~~

where `a₃ = cpChartFactor 3`. The Lean predicate is
`GenuineReadoutControlsSingletonCarryEnergyAt`.

At a Genuine zero, Lean proves the exact audit

~~~math
\mathrm{GenuineReadoutControlsSingletonCarryEnergyAt}(M,p,s)
\quad\Longleftrightarrow\quad
\mathrm{Re}(s)=\frac12.
~~~

The conclusion is unchanged if an arbitrary strictly positive coercivity
coefficient is permitted:

~~~math
\exists\kappa>0,\qquad
\kappa E_{M,p}(s)
\le
\mathrm{normSq}\!\left(a_3(s)\,\mathrm{Genuine}(s)\right).
~~~

At a Genuine zero this also holds exactly when `Re(s) = 1/2`. Therefore the
suggested norm is indeed the correct detector, but proving that its energy is
controlled by the scalar readout on every Genuine zero is the missing kernel
transport itself. Requiring either direct estimate at all Genuine zeros is
equivalent to `GenuineStrongNonvanishingInStrip`.

No inverse of `Genuine`, chosen pseudoinverse, isotropic-membership hypothesis,
or saturation bridge is used in these equivalences.

## Uniform atlas obstruction

For a finite prime atlas `S`, let

~~~math
E_{M,S}(s)=
\left\lVert
  \mathrm{primeGreenBulkFiniteState}(M,s,S)
\right\rVert^2.
~~~

Lean proves

~~~math
\left[
\exists C\ge0,\ \forall S,\quad
E_{M,S}(s)
\le
C\,\mathrm{normSq}\!\left(a_3(s)\,\mathrm{Genuine}(s)\right)
\right]
\quad\Longleftrightarrow\quad
\delta=0.
~~~

More quantitatively, if `Re(s) != 1/2`, then for every proposed real scalar
majorant `B` there is a finite prime atlas with

~~~math
B<E_{M,S}(s).
~~~

Consequently no finite multiple of the scalar Genuine energy uniformly
controls the existing atlas energy off equilibrium. At a hypothetical
off-critical Genuine zero, the scalar side is zero while some finite atlas
has strictly positive energy.

This is not a proof that such a zero exists. It is the exact obstruction any
future noncompensation estimate must overcome: it must prove the scalar-to-
Hilbert transport, not obtain it from finite-atlas compatibility or from the
Pythagorean decomposition after the Green readouts have already been built.

## Public Lean declarations

~~~lean
primeGreenBulkSingletonEnergy_eq_zero_iff_branchDefect_eq_zero
primeGreenBulkSingletonEnergy_eq_zero_iff_re_eq_half
genuineReadoutControlsSingletonCarryEnergyAt_iff_re_eq_half_of_zero
genuineReadoutCoercivelyControlsSingletonCarryEnergyAt_iff_re_eq_half_of_zero
genuineZerosControlSingletonCarryEnergy_iff_strongNonvanishing
genuineZerosHaveCoerciveSingletonCarryEnergyControl_iff_strongNonvanishing
genuineReadoutControlsPrimeGreenAtlasEnergyAt_iff_critical
genuineReadoutControlsPrimeGreenAtlasEnergyAt_iff_branchNormSq
exists_primeGreenAtlas_violating_scalar_majorant_of_re_ne_half
exists_primeGreenAtlas_violating_genuineReadout_majorant_of_re_ne_half
exists_primeGreenAtlas_positive_energy_of_genuine_zero_off_critical
~~~

The implementation is in
[`GenuineCarryEnergyControl.lean`](../NativeCarryC3Crosswalk/GenuineCarryEnergyControl.lean).
All declarations are included in the repository-wide kernel axiom audit.
