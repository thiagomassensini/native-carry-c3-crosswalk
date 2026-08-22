# Completed TFVD ledger and C3--Naimark feasibility

This note records an exact obstruction and the corresponding lossless
realization. It does not introduce a spectral hypothesis or identify two
forms by definition.

## The residual-only obstruction

For the canonical same-edge ordinary/log-jet input, the completed
precompression residual is exactly

```math
R_{M,s}
=
\mathrm{Re}(E_{3M,s})\,(0,e_1).
```

Here `(0,e₁)` is fixed. Therefore every real-linear map `T` satisfies

```math
T(R_{M,s})
=
\mathrm{Re}(E_{3M,s})\,T(0,e_1).
```

The canonical residual family is contained in one real line, and every
linear image of it remains contained in one real line. Consequently the
residual alone cannot linearly reconstruct a general six-coordinate C3 Green
port.
This is a rank statement, not a numerical approximation.

The lossless ledger therefore retains three entries before compression:

1. the ordinary TFVD state;
2. the logarithmic-jet TFVD state;
3. the two-channel precompression residual.

Lean proves that the three projections of the seeded ledger are literally the
existing canonical definitions.

## Six complex coordinates, not six fixed values

The minimal nonempty complete C3 block has three arithmetic cells on each of
its two Green legs. Its port is

```math
(x_{L,0},x_{L,1},x_{L,2};
  x_{R,0},x_{R,1},x_{R,2})\in\mathbb C^6.
```

Thus the carrier has six complex coordinate slots, or twelve real coordinate
slots. This does not say that the canonical family parametrized by `s`
surjects onto the carrier. The dimension belongs to the ambient port; the
canonical states may occupy a lower-dimensional nonlinear subset.

The construction stores all real parts in one realified camera channel and
all imaginary parts in the other. The six camera labels are `2,3,4,5,6,7`.
They are coordinate labels, not prescribed coordinate values. Lean recovers
each of the twelve real coordinates and proves the packing injective.

## Canonical Naimark promotion

The finite-dimensional packing is automatically bounded and defines

```math
Q:\mathbb C^6_{\mathbb R}
  \longrightarrow
  \mathcal H_{\mathrm{cam}}\oplus\mathcal H_{\mathrm{cam}}.
```

Composing it with the coordinatewise Naimark isometry gives

```math
JQ:\mathbb C^6_{\mathbb R}
  \longrightarrow
  \mathcal K_{\mathrm{Naimark}}\oplus
  \mathcal K_{\mathrm{Naimark}}.
```

Lean proves:

- `Q` is injective;
- `JQ` is injective;
- the canonical Naimark adjoint readout recovers `Q` exactly;
- the coordinatewise Naimark isometry preserves the realified Green skew
  form exactly.

The last statement is the precise preservation law supplied by the Naimark
geometry. It does not yet identify the completed TFVD residual scalar with
the finite C3 Green form. A map intertwining the uncollapsed TFVD ledger with
the complete C3 port remains separate analytic data; the rank-one audit shows
why it cannot be manufactured from the collapsed residual alone.

## Lean declarations

The implementation is in
`NativeCarryC3Crosswalk/CompletedTfvdNaimarkFeasibility.lean`. Its principal
declarations are:

```lean
seededCompletedTfvdGreenLedger_residual_eq_smul
map_seededCompletedTfvdGreenLedger_residual_eq_smul
c3CameraFinsuppPairLinearMap_injective
c3SixCameraPacking_injective
c3SixCameraNaimarkRealization_injective
canonicalCameraStateReadout_c3SixCameraNaimarkRealization
realifiedGreenSkew_realifiedNaimarkPort
realifiedGreenSkew_c3SixCameraNaimarkRealization
```
