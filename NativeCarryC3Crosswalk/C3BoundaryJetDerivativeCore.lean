import NativeCarryC3Crosswalk.C3BoundaryJetCore
import NativeCarrySpectralWeyl.Camera.Factors

/-!
# Exponent and native-time derivatives of the C3 boundary jet

The oriented C3 ledger uses the same fifth-order spatial jet for the
resultant and for its time derivative.  This module differentiates the
recurrent spatial coefficients and proves that the resulting explicit jet is
the genuine derivative, first in the complex exponent and then along
`s = 1/2 + it`.
-/

namespace NativeCarryC3Crosswalk

open NativeCarrySpectralWeyl.Camera

noncomputable section

/--
`HasDerivAt` specialized to the normed-algebra structure used by the complex
product rule.  This is definitionally the ordinary derivative predicate; the
explicit specialization prevents competing bundled complex-space instances
from changing elaboration after downstream imports.
-/
abbrev ComplexAlgebraHasDerivAt (f : ℂ → ℂ) (f' x : ℂ) : Prop :=
  @HasDerivAt ℂ _ ℂ
    Complex.instNormedField.toNormedCommRing.toAddCommGroup
    (NormedAlgebra.toNormedSpace ℂ).toModule _ _ f f' x

/-- Exponent derivative of the recurrent spatial coefficient. -/
def dirichletSpaceCoefficientExponentDeriv (s : ℂ) : ℕ → ℂ
  | 0 => 0
  | order + 1 =>
      dirichletSpaceCoefficientExponentDeriv s order *
          (-s - (order : ℂ)) -
        dirichletSpaceCoefficient s order

@[simp] theorem dirichletSpaceCoefficientExponentDeriv_zero (s : ℂ) :
    dirichletSpaceCoefficientExponentDeriv s 0 = 0 := rfl

@[simp] theorem dirichletSpaceCoefficientExponentDeriv_succ
    (s : ℂ) (order : ℕ) :
    dirichletSpaceCoefficientExponentDeriv s (order + 1) =
      dirichletSpaceCoefficientExponentDeriv s order *
          (-s - (order : ℂ)) -
        dirichletSpaceCoefficient s order := rfl

/-- The recurrent coefficient derivative is the actual complex derivative. -/
theorem dirichletSpaceCoefficient_hasDerivAt (order : ℕ) (s : ℂ) :
    ComplexAlgebraHasDerivAt (fun z => dirichletSpaceCoefficient z order)
      (dirichletSpaceCoefficientExponentDeriv s order) s := by
  induction order with
  | zero =>
      simpa using hasDerivAt_const s (1 : ℂ)
  | succ order inductionHypothesis =>
      have hfactor :
          ComplexAlgebraHasDerivAt
            (fun z : ℂ => -z - (order : ℂ)) (-1) s :=
        (hasDerivAt_neg' s).sub_const (order : ℂ)
      have hproduct := inductionHypothesis.mul hfactor
      simp only [dirichletSpaceCoefficient_succ,
        dirichletSpaceCoefficientExponentDeriv_succ]
      have hproduct' :
          ComplexAlgebraHasDerivAt
            ((fun z => dirichletSpaceCoefficient z order) *
              fun z : ℂ => -z - (order : ℂ))
            (dirichletSpaceCoefficientExponentDeriv s order *
                (-s - (order : ℂ)) -
              dirichletSpaceCoefficient s order) s := by
        apply hproduct.congr_deriv
        ring
      apply hproduct'.congr_of_eventuallyEq
      filter_upwards with z
      rfl

/-- Explicit exponent derivative of the `order`-th spatial kernel. -/
def dirichletKernelHigherExponentDeriv
    (order : ℕ) (s : ℂ) (x : ℝ) : ℂ :=
  (dirichletSpaceCoefficientExponentDeriv s order -
      dirichletSpaceCoefficient s order * (Real.log x : ℂ)) *
    (x : ℂ) ^ (-s - (order : ℂ))

/-- The explicit higher-kernel exponent derivative is exact for positive `x`. -/
theorem dirichletKernelHigherDeriv_hasDerivAt_exponent
    (order : ℕ) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ComplexAlgebraHasDerivAt
      (fun z => dirichletKernelHigherDeriv order z x)
      (dirichletKernelHigherExponentDeriv order s x) s := by
  have hcoefficient := dirichletSpaceCoefficient_hasDerivAt order s
  have hexponent :
      HasDerivAt (fun z : ℂ => -z - (order : ℂ)) (-1) s :=
    (hasDerivAt_neg' s).sub_const (order : ℂ)
  have hxComplex : (x : ℂ) ≠ 0 := by
    exact_mod_cast hx.ne'
  have hpower := hexponent.const_cpow (Or.inl hxComplex)
  have hproduct := hcoefficient.mul hpower
  unfold dirichletKernelHigherDeriv dirichletKernelHigherExponentDeriv
  rw [Complex.ofReal_log hx.le]
  convert hproduct using 1
  · funext z
    rfl
  · ring

/-- Exponent derivative of the literal fifth-order oriented C3 boundary jet. -/
def c3OrientedBoundaryJetExponentDeriv (cutoff : ℕ) (s : ℂ) : ℂ :=
  -(dirichletKernelHigherExponentDeriv 1 s (c3BoundaryCenter cutoff)) / 3
    + dirichletKernelHigherExponentDeriv 2 s (c3BoundaryCenter cutoff) / 2
    - 5 * dirichletKernelHigherExponentDeriv 3 s
        (c3BoundaryCenter cutoff) / 18
    + dirichletKernelHigherExponentDeriv 4 s
        (c3BoundaryCenter cutoff) / 24
    + dirichletKernelHigherExponentDeriv 5 s
        (c3BoundaryCenter cutoff) / 60

/-- The explicit exponent jet is the derivative of the original boundary jet. -/
theorem c3OrientedBoundaryJet_hasDerivAt_exponent
    (cutoff : ℕ) (s : ℂ) :
    ComplexAlgebraHasDerivAt (c3OrientedBoundaryJet cutoff)
      (c3OrientedBoundaryJetExponentDeriv cutoff s) s := by
  have hcenter := c3BoundaryCenter_pos cutoff
  have h1 := dirichletKernelHigherDeriv_hasDerivAt_exponent 1 s hcenter
  have h2 := dirichletKernelHigherDeriv_hasDerivAt_exponent 2 s hcenter
  have h3 := dirichletKernelHigherDeriv_hasDerivAt_exponent 3 s hcenter
  have h4 := dirichletKernelHigherDeriv_hasDerivAt_exponent 4 s hcenter
  have h5 := dirichletKernelHigherDeriv_hasDerivAt_exponent 5 s hcenter
  have hthird := (h3.const_mul 5).div_const 18
  have hjet :=
    (((h1.neg.div_const 3).add (h2.div_const 2)).sub hthird).add
      (h4.div_const 24)
  have htotal := hjet.add (h5.div_const 60)
  convert htotal using 1
  · funext z
    rfl
  · simp only [c3OrientedBoundaryJetExponentDeriv]

/-- The native line has constant real derivative `I`. -/
theorem nativeLine_hasDerivAt (time : ℝ) :
    HasDerivAt nativeLine Complex.I time := by
  have hid : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 time :=
    (hasDerivAt_id time).ofReal_comp
  have hline :=
    (hasDerivAt_const time (1 / 2 : ℂ)).add
      (hid.mul_const Complex.I)
  have hlineFunction :
      ((fun _u : ℝ => (1 / 2 : ℂ)) +
          fun u : ℝ => (u : ℂ) * Complex.I) = nativeLine := by
    funext u
    simp only [Pi.add_apply, nativeLine]
  rw [hlineFunction] at hline
  simpa only [zero_add, one_mul] using hline

/-- Explicit first time derivative `J_M^(1)` used by the C3 ledger. -/
def c3OrientedBoundaryJetTimeDeriv (cutoff : ℕ) (time : ℝ) : ℂ :=
  c3OrientedBoundaryJetExponentDeriv cutoff (nativeLine time) * Complex.I

/-- `J_M^(1)` is exactly the derivative of `J_M^(0)` along the native line. -/
theorem c3OrientedBoundaryJet_nativeLine_hasDerivAt
    (cutoff : ℕ) (time : ℝ) :
    HasDerivAt
      (fun u : ℝ => c3OrientedBoundaryJet cutoff (nativeLine u))
      (c3OrientedBoundaryJetTimeDeriv cutoff time) time := by
  have hcomp :=
    (c3OrientedBoundaryJet_hasDerivAt_exponent cutoff (nativeLine time)).scomp
      time (nativeLine_hasDerivAt time)
  convert hcomp using 1
  all_goals first
    | with_reducible_and_instances rfl
    | rfl
    | simp only [smul_eq_mul, c3OrientedBoundaryJetTimeDeriv]; ring

end

end NativeCarryC3Crosswalk
