# Two-variable C3 Green--gamma audit

This checkpoint formalizes the exact contribution of the supplied
two-variable analysis and separates it from the still-missing completed trace
identification.

## What closes

For independent complex parameters `r` and `s`, define the finite raw C3
horizontal Gram and Green pairing by

```math
K_M(r,s)=\sum_{n<M}\overline{h_n(r)}h_n(s),
```

```math
B_M(r,s)=\sum_{n<M}
  \left(
    \overline{h_n(r)}g_n(s)
    -\overline{g_n(r)}h_n(s)
  \right),
```

where `g_n(s)=3^{-s}h_n(s)`. Lean proves the cross-multiplied identity

```math
B_M(r,s)=
\left(3^{-s}-\overline{3^{-r}}\right)K_M(r,s).
```

The theorem is
`c3RawGreenPairing_eq_eigenvalueDifference_mul_gammaGram`.  Its
height-coordinate specialization is also exported, and the diagonal Gram
energy is proved nonnegative at every finite cutoff.

## What this does not identify

The boundary response in this identity is the raw camera eigenvalue
`3^{-s}`.  The desired completed response is the logarithmic derivative of
the completed scalar characteristic.  Those are not related by a coordinate
rename.

Two kernel-level obstructions are retained explicitly:

1. scalar synthesis contains a genuine off-diagonal Wronskian sector;
2. the logarithmic-jet wedge differs from the raw Green wedge already on the
   first edge.

The audited declarations are
`c3ScalarSynthesis_not_universally_greenDiagonal` and
`c3LogJetChannel_not_absorbed_by_rawGreen_at_zero`.

## Exact remaining gate

The global route needs one construction that places the completed value,
completed log jet, and spectral defect equation on the same state:

```math
\Gamma_0 f_z=F(z),\qquad
\Gamma_1 f_z=-F'(z),\qquad
T^*f_z=z f_z.
```

Equivalently, without division,

```math
F'(w)^*F(z)-F(w)^*F'(z)
  =(z-\bar w)\langle f_w,f_z\rangle
```

with the orientation adjusted to the repository Green convention.

The numerical audits verify the raw C3 factorization, the algebraic
Wronskian quotient, and the finite Jacobi projective tower separately.  They
do not verify this completed trace equality.  The projective tower also
starts after all-order Hankel positivity has been supplied, so it cannot be
used as that positivity proof without an additional argument.
