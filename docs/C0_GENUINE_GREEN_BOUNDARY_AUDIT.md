# C0 Genuine / Green boundary identity audit

## Question

Can the historical nonzero C2 factor `C0` close the missing structural
identity between the Genuine scalar readout and the fixed reflected Green
boundary relation, without assuming a zero or an equivalent form of
confinement?

The audit was performed in the pinned Lean environment of this repository.
No zero hypothesis, critical-line hypothesis, strong nonvanishing statement,
or isotropic-membership hypothesis is used in the universal identities below.

## Exact factors and types

The pinned `CPFormal` API calls the historical C2 vertical factor
`pairedBridgeFactor`. This repository exposes it as

```lean
c0VerticalFactor : ℂ → ℂ
```

and reuses the existing kernel-checked theorem that it is nonzero throughout
the open Genuine strip.

The canonical C3 scalar boundary trace converges to

```math
Chart_3(s)=a_3(s) Genuine(s),
```

where `a₃(s) = cpChartFactor 3 s` is also nonzero in that strip. Therefore
the camera-change dressing

```math
d_{0←3}(s)=C_0(s)/a_3(s)
```

is well defined and nonzero there. The dressed finite trace

```math
T_{0,M}(s)=d_{0←3}(s) T_{3,M}(s)
```

converges exactly to the C2 central Genuine numerator

```math
C_0(s) Genuine(s).
```

This is the linear readout supplied by `finiteC0GenuineBoundaryTrace`.

The reflected Green form is sesquilinear, not linear. Its type-correct scalar
comparison is consequently the reflected product

```math
P_{0,M}(s)=conj(T_{0,M}(s)) T_{0,M}(s^#),
    s^#=1-conj(s).
```

Lean proves its limit before any zero is considered:

```math
P_{0,M}(s) →
conj(C_0(s) Genuine(s)) C_0(s^#) Genuine(s^#).
```

## Strongest universal identity

Write

```math
r_3(s)=D_3(Re(s)-1/2)
```

for the existing radial carry coefficient, `G_M(s)` for the reflected C3
Green form, and `R_M(s)` for the already-defined complete angular provenance
correction. Lean proves for every complex parameter and every finite cutoff:

```math
r_3(s) P_{0,M}(s)
=
conj(d_{0←3}(s)) d_{0←3}(s^#)
(G_{3M}(s)+r_3(s)R_M(s)).
```

This is the exact C0 Genuine / Green identity available from the current
carrier. It is an identity for arbitrary parameters, not a statement about
zeros.

Because both camera dressings are nonzero in the open strip, Lean also proves
the exact reduction

```math
r_3(s)P_{0,M}(s)
=
conj(d_{0←3}(s))d_{0←3}(s^#)G_{3M}(s)

⇔

r_3(s)R_M(s)=0.
```

Therefore nonvanishing of `C0` permits cancellation of the vertical dressing,
but it does not prove that the provenance correction vanishes. Dropping that
term would insert the unresolved assertion rather than derive it.

## Finite obstruction with C0 present

The existing two-cell witness is

```math
x=((1,-1),0).
```

Scalar synthesis sends its first leg to zero. Multiplication by `C0` happens
after that synthesis, so the C0-dressed Genuine readout also sends `x` to
zero for every complex parameter. However, `x` is not in the fixed diagonal
Green relation.

Lean therefore proves that no boundary defect whose zero set is exactly that
relation can factor through the two C0-dressed coarse Genuine scalars alone.
This theorem has no strip hypothesis and does not need `C0 ≠ 0`: multiplying a
discarded coordinate by a nonzero scalar cannot reconstruct it.

## Relation to the nonlocal arithmetic trace

The closed nonlocal trace `J_arith` constructed in
`ArithmeticNonlocalTrace.lean` remains valid. Its graph port preserves the
prime-camera mass and upgraded Green output, and its own graph defect vanishes
identically by construction.

That graph Green form is not yet identified with the reflected C3 Green form
appearing above. Treating the two forms as equal would make the graph defect
zero for every parameter and would erase the radial detector. The missing
crosswalk must therefore transport the full provenance correction, or an
equivalent nonlocal endpoint/tail coordinate, in addition to the scalar
`C0 * Genuine` readout.

## Kernel-checked declarations

```lean
c0VerticalFactor_ne_zero
c0ToC3BoundaryDressing_ne_zero
finiteC0GenuineBoundaryTrace_tendsto
finiteC0GenuineBoundaryPairing_tendsto
radialScaledAngularScalarPairing_eq_greenForm_add_correction
radialScaledC0GenuineBoundaryPairing_eq_dressedGreen_add_correction
radialScaledC0GenuineBoundaryPairing_eq_pureGreen_iff_correction_eq_zero
finiteC0GenuineCoarseReadout_apply
no_finiteC3_boundaryDefect_factorization_through_c0GenuineReadout
```

## Conclusion

`C0` closes the vertical normalization and is nonzero in the relevant strip.
It does not close the Green provenance channel. The exact unconditional
identity is the corrected ledger above; a pure `C0 Genuine = Green defect`
factorization through scalar synthesis is obstructed already at two cells.

