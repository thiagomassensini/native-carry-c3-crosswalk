# Structural carry--TFVD--Green defect principle

This note records the causal order of the construction. The equilibrium is
not selected by a zero.

## Before Green and before zeros

The positional carry geometry first defines the quadratic branch norm and
its defect

```math
b_p(\sigma)=\mathrm{branchNormSq}(p,\sigma)-1.
```

For a prime camera and positive `sigma`, Lean already proves

```math
b_p(\sigma)=0
\quad\Longleftrightarrow\quad
\sigma=\frac12.
```

This theorem mentions no Genuine function, zero predicate, TFVD boundary
condition, or Green relation.

The next construction is TFVD. The C3 crosswalk proves for every complex
parameter and finite cutoff that the differentiated Genuine bracket, the
TFVD diagonal, and the Green boundary form are one finite computation:

```math
\mathrm{greenForm}
\left(B_M(s),B_M(s^\#)\right)
=
\mathrm{TFVDDiagonal}_{3,M}(s).
```

Thus Green does not introduce the positional obstruction. It is a later
boundary readout of the TFVD computation.

## Structural defect energy

In the open strip, the infinite reflected Green energy is strictly positive.
The structural defect energy is defined by

```math
\mathcal D_p(s)
=
\left(
E_\infty(s)b_p(\mathrm{Re}(s))
\right)^2.
```

No zero hypothesis occurs in this definition. Lean proves

```math
\mathcal D_p(s)\ge0,
```

```math
\mathcal D_p(s)=0
\quad\Longleftrightarrow\quad
\mathrm{C3PositionalGeometryCompatible}(\mathrm{Re}(s))
\quad\Longleftrightarrow\quad
\mathrm{Re}(s)=\frac12,
```

and

```math
\mathrm{Re}(s)\ne\frac12
\quad\Longleftrightarrow\quad
\mathcal D_p(s)>0.
```

On the equilibrium line the energy vanishes identically for every phase
time, independently of any zero:

```math
\mathcal D_p\!\left(\frac12+it\right)=0.
```

## What a completed zero can and cannot do

The enriched tail-completed readout keeps the Genuine/TFVD tail and the
structural branch defect as orthogonal coordinates. Its norm satisfies

```math
\mathcal D_p(s)
\le
\left\lVert\mathcal C_{M,p}(s)\right\rVert^2.
```

Therefore Lean proves without a Genuine-zero hypothesis:

```math
\mathcal C_{M,p}(s)=0
\quad\Longrightarrow\quad
\mathcal D_p(s)=0
\quad\Longrightarrow\quad
\mathrm{Re}(s)=\frac12.
```

This is the precise formal meaning of structural necessity: a zero of the
completed geometric port does not push the parameter onto the equilibrium
line. The port can vanish only after the prior positional defect has already
vanished.

The statement is deliberately not changed into

```math
\mathrm{Genuine}(s)=0
\quad\Longrightarrow\quad
\mathcal D_p(s)=0.
```

That implication is the still-open scalar-to-completed activation gate. The
present theorem proves the structural obstruction and the no-cancellation
geometry without hiding that later gate in the definition of a zero.

## Public Lean declarations

```lean
structuralCarryGreenDefectEnergy
structuralCarryGreenDefectEnergy_nonneg
structuralCarryGreenDefectEnergy_eq_zero_iff_branchDefect
structuralCarryGreenDefectEnergy_eq_zero_iff_compatible
structuralCarryGreenDefectEnergy_eq_zero_iff_re_eq_half
structuralCarryGreenDefectEnergy_criticalLine
structuralCarryGreenDefectEnergy_pos_iff_re_ne_half
structuralCarryGreenDefectEnergy_le_completedReadout_norm_sq
completedReadout_zero_implies_structuralDefect_zero
completedReadout_zero_implies_re_eq_half
genuineBracket_tfvd_green_structuralDefect_capstone
```

