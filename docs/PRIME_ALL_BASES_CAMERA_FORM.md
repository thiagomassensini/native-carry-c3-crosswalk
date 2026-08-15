# Prime-to-all-bases camera form bridge

This note records the typed bridge from finite prime-camera coefficients to
the intrinsic all-bases Gram completion. The construction is valid for
arbitrary bounded core maps. It assumes no zero, critical line, vanishing
tilt, Green isotropy, or confinement statement.

## The native target remains real

The native operator takes values in the two-coordinate real plane. The
upstream C3/CP theorem
`nativeCarryRealPlaneComplexPackaging_eq_equivRealProdCLM_symm` proves that
its complex notation is literally the inverse-coordinate map associated with
`Complex.equivRealProdCLM`.

The crosswalk now proves that this coordinate packaging commutes with the
all-bases completion:

```math
\mathrm{extend}\!\left(\mathrm{pack}\circ q\right)
=
\mathrm{pack}\circ\mathrm{extend}(q).
```

It follows after completion that

```math
\mathrm{pack}(Q u)=0
\quad\Longleftrightarrow\quad
Q u=0,
```

and that the packaged squared norm is exactly the native real quadratic
energy:

```math
\mathrm{normSq}\!\left(\mathrm{pack}(Q u)\right)
=
\mathrm{energy}_{\mathbb R^2}(Q u).
```

Thus the complex coordinate does not define a second operator, a second zero
predicate, or a second energy.

## Finite prime core inside the all-bases core

Let `CameraFinsupp` be the finitely supported all-bases camera core. Prime
labels embed canonically into all camera labels:

```lean
primeCameraIndexEmbedding : Nat.Primes ↪ CameraIndex
```

Reindexing finite prime coefficients gives an injective linear map

```math
\iota_{\mathbb P}:
c_{00}(\mathbb P;\mathbb R)
\longrightarrow
\mathrm{CameraFinsupp}.
```

The selected prime carrier is the range of this map equipped with the norm it
inherits from the intrinsic all-bases Gram geometry:

```lean
PrimeCameraGramCore := LinearMap.range primeCameraCoreReindex
```

No completed unweighted prime norm is imposed at this step.

## Exact extension

Every bounded real functional on `PrimeCameraGramCore` extends first to the
full algebraic camera core by Hahn--Banach and then uniquely to
`CameraHilbert`. Lean proves exact agreement on prime-supported vectors and
exact preservation of the operator norm.

The native two-coordinate version is also kernel checked. A bounded map

```math
q:
\mathrm{PrimeCameraGramCore}
\longrightarrow
\mathbb R^2
```

is extended coordinatewise, reassembled as the same real pair, and then
completed. The resulting all-bases map satisfies

```math
\widehat q\!\left(\mathrm{cameraEmbedding}(\iota_{\mathbb P}u)\right)
=q(u),
\qquad
\lVert\widehat q\rVert=\lVert q\rVert.
```

Packaging this result into complex notation is governed by the commuting
identity above; it adds no channel.

## Why the raw prime synthesis is not the bridge

For every odd prime `p`, Lean computes the diagonal Gram value exactly:

```math
\left\lVert v_p\right\rVert^2
=
K(p,p)
=
p(p-1).
```

The axes of the existing unweighted prime Hilbert space have norm one.
Therefore there is no bounded linear operator sending every such axis to the
raw all-bases camera vector:

```lean
no_bounded_rawPrimeCameraAxis_synthesis
```

This is not a failure of the prime-to-all-bases inclusion. It identifies the
necessary normalization: boundedness must be proved in the intrinsic Gram
norm, not inherited from an unrelated unweighted `ℓ²` norm.

## Remaining analytic gate

The reusable topology and the typed prime inclusion are now closed. The
research-specific input still missing is a definition of the enriched
Green/Haar core map

```math
q_{\mathrm{GH}}:
\mathrm{PrimeCameraGramCore}
\longrightarrow
\mathbb R^2
```

together with a uniform intrinsic Gram estimate

```math
\lVert q_{\mathrm{GH}}(u)\rVert
\le C\lVert u\rVert_{\mathrm{Gram}}.
```

Once that estimate is proved, the extension theorems apply automatically.
Nothing in the present bridge turns scalar Genuine vanishing into Green
closure or proves global confinement.

