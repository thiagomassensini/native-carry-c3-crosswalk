# Native Carry C3 Crosswalk

Lean 4 integration layer proving that the pinned finite native real operator
and the pinned finite bracket characteristic are literally the same finite
computation in two coordinate presentations. It also materializes the exact
fifth-order C3 boundary correction, its first time derivative, and the exact
stationary equation used by the certified residual ledgers.

The construction introduces no new zero predicate, analytic continuation,
limit hypothesis, or spectral assumption.

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

These are finite algebraic identities. They do not assert convergence of the
C3 corrected residual, existence of a limiting zero, or confinement of any
infinite zero set.

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

The scalar function `c3CorrectedCoreError M t` is exactly
the norm of the corrected complex residual. Once a corrected stationary
center `c_M` has been constructed, the ledger quantity is obtained by
evaluating this function at `t = c_M`.

This package deliberately does **not** choose `c_M` from floating-point
output, assert existence or uniqueness of such a center uniformly in `M`, or
prove `c3CorrectedCoreError M (c_M) → 0`. Those are the remaining analytic
obligations, not consequences of the finite crosswalk and stationary
identity.

## Pinned foundations

| Package | Revision |
|---|---|
| `CPFormal` | `537028681ae6a775c083a1e2fb6e67db24697b82` (`v0.62.0`) |
| `NativeCarrySpectralWeyl` | `ca726315be2eb9b421c07224a07967d02d07f0fb` (`v0.53.0`) |
| `FiniteNativeCarryOperator` | `00e9d6beb17226545abf5ddf90bbfede6c7146b0` (`v0.1.0`, transitive pin) |
| `GreenFrame` | `cd2d838bee67ad23f869a02f8ed9f0a0feb926fa` (`v2.1.0`, transitive pin) |
| Lean / Mathlib | `v4.32.0` |

## Audit

Run the complete local audit with:

```bash
bash scripts/audit.sh
```

The audit builds with warnings as errors, rejects local trust escapes, checks
GitHub Markdown, and evaluates `#print axioms` for every public theorem. The
dependency allowlist is restricted to `propext`, `Classical.choice`, and
`Quot.sound`.
