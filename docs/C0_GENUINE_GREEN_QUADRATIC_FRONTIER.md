# Quadratic C0--Genuine / Green frontier

## Question

Can the quadratic carry norm and the nonzero vertical factor `C0` be combined
with the reflected Green defect without assuming the desired confinement?

Yes, for the completed two-channel port. No, not as an identification of the
scalar Genuine kernel with the completed kernel.

## Unconditional identity

For a prime camera `p`, define

```math
D_p(s)
=r_p\!\left(\mathrm{Re}(s)-\frac12\right)
 E_{\mathrm{Green}}(s),
```

where the reflected Green energy is strictly positive throughout the open
Genuine strip. The completed quadratic energy is

```math
\mathcal E_p(s)
=\mathrm{normSq}\!\left(C_0(s)\,\mathrm{Genuine}(s)\right)
+D_p(s)^2.
```

Lean proves this identity before any zero is considered. It also expands the
first term using the native factorization

```math
\mathrm{normSq}\!\left(C_0(s)\,\mathrm{Genuine}(s)\right)
=\mathrm{normSq}(C_0(s))
 \mathrm{normSq}(\mathrm{Genuine}(s)).
```

No inverse, chosen representative, zero hypothesis, critical-line hypothesis,
or nonvanishing conclusion is used.

## Quantitative coercivity

The existing radial theorem gives

```math
2|\delta|\log(p)\le |r_p(\delta)|.
```

Multiplying by the positive reflected Green energy and squaring yields the
kernel-checked bound

```math
\left(2|\delta|\log(p)E_{\mathrm{Green}}(s)\right)^2
\le \mathcal E_p(s).
```

Consequently, the completed energy is strictly positive whenever
`Re(s) != 1/2`, independently of the scalar Genuine value.

## Exact kernel

Because both summands are nonnegative and the reflected Green energy is
strictly positive, Lean proves

```math
\mathcal E_p(s)=0
\quad\Longleftrightarrow\quad
\mathrm{Genuine}(s)=0
\quad\mathrm{and}\quad
\mathrm{Re}(s)=\frac12.
```

This is the kernel of the completed port. It is not yet a theorem about the
kernel of the scalar coordinate alone.

## What happens at a hypothetical off-critical scalar zero

If `Genuine(s) = 0`, the identity reduces exactly to

```math
\mathcal E_p(s)=D_p(s)^2.
```

Therefore, if additionally `Re(s) != 1/2`, then

```math
\mathcal E_p(s)>0.
```

There is no contradiction: the scalar coordinate vanishes while the Green
coordinate retains all completed energy. This is precisely what a direct sum
is allowed to do.

## Circularity firewall

The remaining implication would be

```math
\mathrm{Genuine}(s)=0
\Longrightarrow
\mathcal E_3(s)=0.
```

The proposition `GenuineZerosCloseC0GenuineGreenCompletedEnergy` records that
concrete statement. Lean proves

```math
\mathrm{GenuineZerosCloseC0GenuineGreenCompletedEnergy}
\quad\Longleftrightarrow\quad
\mathrm{GenuineStrongNonvanishingInStrip}.
```

Thus quoting the quadratic norm is not circular. Treating scalar closure as
closure of the completed norm without an independent intertwiner would be.

## Public declarations

```lean
normSq_genuineCentralContinuationC2_eq_c0_mul_genuine
c0GenuineGreenCompletedEnergy_eq_sum_of_squares
c0GenuineGreenCompletedEnergy_nonneg
c0GenuineGreenRadialDefect_eq_zero_iff
c0GenuineGreenCompletedEnergy_eq_zero_iff
c0GenuineGreenCompletedEnergy_eq_zero_iff_re_eq_half
c0GenuineGreenCompletedEnergy_ge_radial_coercive_square
c0GenuineGreenCompletedEnergy_pos_of_re_ne_half
c0GenuineGreenCompletedEnergy_eq_greenDefect_sq_of_genuine_zero
c0GenuineGreenCompletedEnergy_pos_of_genuine_zero_off_critical
genuineZerosCloseC0GenuineGreenCompletedEnergy_iff_strongNonvanishing
```
