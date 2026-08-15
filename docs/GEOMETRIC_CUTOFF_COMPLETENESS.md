# Geometric cutoff completeness

The finite native cutoff is indexed by complete bracket centers. It is not a
raw upper bound on the integer variable.

For one retained center, every radius in the camera is emitted together with
both of its legs:

~~~math
c-r,\qquad c,\qquad c+r.
~~~

Consequently, retaining `M` centers requires the right end-cap of the last
center as part of the finite object.

## Exact horizons

For the exceptional aligned C2 camera, the centers are `4, 8, ..., 4M` and
the radius is `1`. Its exact horizon is

~~~math
H_2(M)=4M+1.
~~~

For every natural camera `b >= 3`, the centers are `b, 2b, ..., bM` and the
radii are

~~~math
1,\ldots,\left\lfloor\frac b2\right\rfloor.
~~~

Its exact horizon is therefore

~~~math
H_b(M)=bM+\left\lfloor\frac b2\right\rfloor.
~~~

Lean proves that every left leg remains positive, every right leg lies below
this horizon, and the largest right leg of the last center is exactly the
horizon. Stopping at `bM` cuts a nonempty right leg and is not a complete
camera cutoff.

With a fixed raw horizon `N`, the maximal number of complete centers is

~~~math
M_2(N)=\left\lfloor\frac{N-1}{4}\right\rfloor
~~~

for C2, and

~~~math
M_b(N)=
\left\lfloor
\frac{N-\lfloor b/2\rfloor}{b}
\right\rfloor
~~~

for `b >= 3`, with natural-number subtraction returning zero before the
boundary width fits. In particular, a natural camera is not geometrically
active until

~~~math
N\ge b+\left\lfloor\frac b2\right\rfloor.
~~~

For an initial atlas through `B`, one horizon containing `M` complete centers
of every supported camera is

~~~math
H_{\le B}(M)=
\max\left(4M+1,\;BM+\left\lfloor\frac B2\right\rfloor\right).
~~~

This is the correct way to compare high-base cameras at a common raw
horizon. A camera with no complete center is inactive; it has not produced a
zero measurement.

## Two different tails

The word *tail* refers to two related but distinct pieces.

1. The finite right end-cap consists of the legs after the last center and up
   to `H_b(M)`. It belongs to the finite head itself.
2. The analytic tail consists of centers `M, M+1, ...` in zero-based Lean
   indexing. Every term of this tail is another complete center bracket.

Lean proves the exact identity

~~~math
\chi_{b,M}(s)
+
\sum_{k\ge0} C_{b,M+k}(s)
=
\chi_b(s),
~~~

where `C_{b,j}` is the entire bracket at center `j`, including both legs.
Throughout the common scalar domain this becomes

~~~math
\chi_{b,M}(s)
+
\sum_{k\ge0} C_{b,M+k}(s)
=
a_b(s)Z_{\mathrm{native}}(s).
~~~

This equality is proved for arbitrary parameters. It assumes no zero,
critical line, tilt cancellation, or Green isotropy.

If the common scalar vanishes, the exact consequence is

~~~math
\chi_{b,M}(s)
=
-\sum_{k\ge0} C_{b,M+k}(s).
~~~

Thus the tail is accounted for rather than discarded.

## Even-camera endpoint

For an even natural camera, the antipodal endpoint

~~~math
bM+\frac b2
~~~

is the right leg of the last retained center and also the future left leg of
the first omitted center. Its finite coefficient is `1`, while its periodic
infinite coefficient is `2`. Lean keeps this as an explicit head--tail
incidence. It is not silently normalized away.

## Exact logical scope

Camera completeness removes artificial errors caused by cutting a bracket in
half. It makes the finite telescope and its analytic tail well typed and
camera aware.

It does not by itself prove that the surviving central defect cannot be
compensated by the complete analytic tail or by another carrier channel. That
later statement requires positivity, orthogonality, or a coercive estimate on
the enriched ledger. The present module isolates cutoff completeness so that
such an estimate cannot win by omitting a leg or a high-base end-cap.

## Public Lean declarations

~~~lean
IsGeometricallyCompleteNativeCutoff
completeCenterCount
initialAtlasCompleteHorizon
included_center_has_both_legs_in_window
last_right_leg_eq_finiteCameraWindow
center_only_horizon_is_not_complete
natural_one_complete_center_iff
finiteCameraWindow_le_initialAtlasCompleteHorizon
even_endpoint_records_head_tail_incidence
complete_head_add_complete_center_tail_of_mem_domain
complete_head_add_complete_center_tail_eq_factor_mul_nativeScalar
finite_head_eq_neg_complete_center_tail_of_nativeScalar_zero
~~~
