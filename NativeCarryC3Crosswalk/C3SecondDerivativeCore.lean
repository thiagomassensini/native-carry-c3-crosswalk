import NativeCarryC3Crosswalk.C3BoundaryJetDerivativeCore
import NativeCarrySpectralWeyl.Camera.DerivativeTail

/-!
# Second native-time derivative of the corrected C3 chart

The stationary-localization ledger controls the derivative of
`h_M = A_M · B_M`.  This requires the corrected acceleration.  This module
differentiates the already explicit exponent derivatives once more and proves
that every resulting formula is an actual derivative.
-/

namespace NativeCarryC3Crosswalk

open NativeCarrySpectralWeyl.Camera
open FiniteNativeCarryOperator.Camera

noncomputable section

/-! ## Second exponent derivative of the spatial jet -/

/-- Second exponent derivative of the recurrent spatial coefficient. -/
def dirichletSpaceCoefficientExponentSecondDeriv (s : ℂ) : ℕ → ℂ
  | 0 => 0
  | order + 1 =>
      dirichletSpaceCoefficientExponentSecondDeriv s order *
          (-s - (order : ℂ)) -
        2 * dirichletSpaceCoefficientExponentDeriv s order

@[simp] theorem dirichletSpaceCoefficientExponentSecondDeriv_zero (s : ℂ) :
    dirichletSpaceCoefficientExponentSecondDeriv s 0 = 0 := rfl

@[simp] theorem dirichletSpaceCoefficientExponentSecondDeriv_succ
    (s : ℂ) (order : ℕ) :
    dirichletSpaceCoefficientExponentSecondDeriv s (order + 1) =
      dirichletSpaceCoefficientExponentSecondDeriv s order *
          (-s - (order : ℂ)) -
        2 * dirichletSpaceCoefficientExponentDeriv s order := rfl

/-- The explicit second coefficient derivative is exact. -/
theorem dirichletSpaceCoefficientExponentDeriv_hasDerivAt
    (order : ℕ) (s : ℂ) :
    ComplexAlgebraHasDerivAt
      (fun z => dirichletSpaceCoefficientExponentDeriv z order)
      (dirichletSpaceCoefficientExponentSecondDeriv s order) s := by
  induction order with
  | zero =>
      simpa using hasDerivAt_const s (0 : ℂ)
  | succ order inductionHypothesis =>
      have hfactor :
          ComplexAlgebraHasDerivAt
            (fun z : ℂ => -z - (order : ℂ)) (-1) s :=
        (hasDerivAt_neg' s).sub_const (order : ℂ)
      have hproduct := inductionHypothesis.mul hfactor
      have hcoefficient := dirichletSpaceCoefficient_hasDerivAt order s
      have htotal := hproduct.sub hcoefficient
      simp only [dirichletSpaceCoefficientExponentDeriv_succ,
        dirichletSpaceCoefficientExponentSecondDeriv_succ]
      have htotal' :
          ComplexAlgebraHasDerivAt
            ((fun z => dirichletSpaceCoefficientExponentDeriv z order) *
                (fun z : ℂ => -z - (order : ℂ)) -
              fun z => dirichletSpaceCoefficient z order)
            (dirichletSpaceCoefficientExponentSecondDeriv s order *
                (-s - (order : ℂ)) -
              2 * dirichletSpaceCoefficientExponentDeriv s order) s := by
        apply htotal.congr_deriv
        ring
      apply htotal'.congr_of_eventuallyEq
      filter_upwards with z
      rfl

/-- Explicit second exponent derivative of the `order`-th spatial kernel. -/
def dirichletKernelHigherExponentSecondDeriv
    (order : ℕ) (s : ℂ) (x : ℝ) : ℂ :=
  (dirichletSpaceCoefficientExponentSecondDeriv s order -
      2 * dirichletSpaceCoefficientExponentDeriv s order *
        (Real.log x : ℂ) +
      dirichletSpaceCoefficient s order * (Real.log x : ℂ) ^ 2) *
    (x : ℂ) ^ (-s - (order : ℂ))

/-- The explicit second higher-kernel exponent derivative is exact. -/
theorem dirichletKernelHigherExponentDeriv_hasDerivAt
    (order : ℕ) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ComplexAlgebraHasDerivAt
      (fun z => dirichletKernelHigherExponentDeriv order z x)
      (dirichletKernelHigherExponentSecondDeriv order s x) s := by
  have hfirst := dirichletSpaceCoefficientExponentDeriv_hasDerivAt order s
  have hcoefficient := dirichletSpaceCoefficient_hasDerivAt order s
  have hlogCoefficient := hcoefficient.mul_const (Real.log x : ℂ)
  have hleft := hfirst.sub hlogCoefficient
  have hexponent :
      HasDerivAt (fun z : ℂ => -z - (order : ℂ)) (-1) s :=
    (hasDerivAt_neg' s).sub_const (order : ℂ)
  have hxComplex : (x : ℂ) ≠ 0 := by
    exact_mod_cast hx.ne'
  have hpower := hexponent.const_cpow (Or.inl hxComplex)
  have hproduct := hleft.mul hpower
  rw [← Complex.ofReal_log hx.le] at hproduct
  unfold dirichletKernelHigherExponentDeriv
    dirichletKernelHigherExponentSecondDeriv
  convert hproduct using 1
  · funext z
    simp only [Pi.sub_apply, Pi.mul_apply]
  · simp only [Pi.sub_apply]
    ring

/-- Second exponent derivative of the literal oriented C3 boundary jet. -/
def c3OrientedBoundaryJetExponentSecondDeriv
    (cutoff : ℕ) (s : ℂ) : ℂ :=
  -(dirichletKernelHigherExponentSecondDeriv 1 s
      (c3BoundaryCenter cutoff)) / 3
    + dirichletKernelHigherExponentSecondDeriv 2 s
        (c3BoundaryCenter cutoff) / 2
    - 5 * dirichletKernelHigherExponentSecondDeriv 3 s
        (c3BoundaryCenter cutoff) / 18
    + dirichletKernelHigherExponentSecondDeriv 4 s
        (c3BoundaryCenter cutoff) / 24
    + dirichletKernelHigherExponentSecondDeriv 5 s
        (c3BoundaryCenter cutoff) / 60

/-- The first exponent derivative of the jet has the displayed second derivative. -/
theorem c3OrientedBoundaryJetExponentDeriv_hasDerivAt
    (cutoff : ℕ) (s : ℂ) :
    ComplexAlgebraHasDerivAt
      (c3OrientedBoundaryJetExponentDeriv cutoff)
      (c3OrientedBoundaryJetExponentSecondDeriv cutoff s) s := by
  have hcenter := c3BoundaryCenter_pos cutoff
  have h1 := dirichletKernelHigherExponentDeriv_hasDerivAt 1 s hcenter
  have h2 := dirichletKernelHigherExponentDeriv_hasDerivAt 2 s hcenter
  have h3 := dirichletKernelHigherExponentDeriv_hasDerivAt 3 s hcenter
  have h4 := dirichletKernelHigherExponentDeriv_hasDerivAt 4 s hcenter
  have h5 := dirichletKernelHigherExponentDeriv_hasDerivAt 5 s hcenter
  have hthird := (h3.const_mul 5).div_const 18
  have hjet :=
    (((h1.neg.div_const 3).add (h2.div_const 2)).sub hthird).add
      (h4.div_const 24)
  have htotal := hjet.add (h5.div_const 60)
  convert htotal using 1
  · funext z
    rfl
  · simp only [c3OrientedBoundaryJetExponentSecondDeriv]

/-- Explicit second native-time derivative `J_M^(2)`. -/
def c3OrientedBoundaryJetTimeSecondDeriv
    (cutoff : ℕ) (time : ℝ) : ℂ :=
  c3OrientedBoundaryJetExponentSecondDeriv cutoff (nativeLine time) *
    Complex.I * Complex.I

/-- `J_M^(2)` is exactly the derivative of `J_M^(1)`. -/
theorem c3OrientedBoundaryJetTimeDeriv_hasDerivAt
    (cutoff : ℕ) (time : ℝ) :
    HasDerivAt (c3OrientedBoundaryJetTimeDeriv cutoff)
      (c3OrientedBoundaryJetTimeSecondDeriv cutoff time) time := by
  have houter :=
    c3OrientedBoundaryJetExponentDeriv_hasDerivAt cutoff (nativeLine time)
  have hcomp := houter.scomp time (nativeLine_hasDerivAt time)
  have htotal := hcomp.mul_const Complex.I
  convert htotal using 1
  all_goals first
    | with_reducible_and_instances rfl
    | rfl
    | simp only [smul_eq_mul, c3OrientedBoundaryJetTimeSecondDeriv]; ring

/-! ## Second exponent derivative of the finite characteristic -/

/-- Second exponent derivative of one positive Dirichlet sample. -/
def dirichletValueExponentSecondDeriv (s : ℂ) (n : ℕ) : ℂ :=
  (Real.log n : ℂ) ^ 2 * dirichletValue s n

/-- The first exponent derivative of a positive sample has the displayed derivative. -/
theorem dirichletValueExponentDeriv_hasDerivAt
    {n : ℕ} (hn : 0 < n) (s : ℂ) :
    ComplexAlgebraHasDerivAt
      (fun z => dirichletValueExponentDeriv z n)
      (dirichletValueExponentSecondDeriv s n) s := by
  have hvalue := dirichletValue_hasDerivAt hn s
  have hscaled := hvalue.const_mul (-(Real.log n : ℂ))
  have hscaled' :
      ComplexAlgebraHasDerivAt
        (fun z => -(Real.log n : ℂ) * dirichletValue z n)
        (dirichletValueExponentSecondDeriv s n) s := by
    apply hscaled.congr_deriv
    unfold dirichletValueExponentSecondDeriv dirichletValueExponentDeriv
    ring
  apply hscaled'.congr_of_eventuallyEq
  filter_upwards with z
  unfold dirichletValueExponentDeriv
  ring

/-- Second exponent derivative of one centered natural bracket. -/
def centeredBracketExponentSecondDerivTerm
    (s : ℂ) (center radius : ℕ) : ℂ :=
  dirichletValueExponentSecondDeriv s (center - radius) -
    2 * dirichletValueExponentSecondDeriv s center +
      dirichletValueExponentSecondDeriv s (center + radius)

/-- Exact derivative of the first exponent derivative of a centered bracket. -/
theorem centeredBracketExponentDerivTerm_hasDerivAt
    (s : ℂ) {center radius : ℕ} (hradius : radius < center) :
    ComplexAlgebraHasDerivAt
      (fun z => centeredBracketExponentDerivTerm z center radius)
      (centeredBracketExponentSecondDerivTerm s center radius) s := by
  have hleft : 0 < center - radius := Nat.sub_pos_of_lt hradius
  have hcenter : 0 < center := hleft.trans_le (Nat.sub_le center radius)
  have hright : 0 < center + radius :=
    hcenter.trans_le (Nat.le_add_right center radius)
  exact ((dirichletValueExponentDeriv_hasDerivAt hleft s).sub
    ((dirichletValueExponentDeriv_hasDerivAt hcenter s).const_mul 2)).add
      (dirichletValueExponentDeriv_hasDerivAt hright s)

/-- Second exponent derivative of one aligned camera-center block. -/
def centerBracketExponentSecondDeriv
    (camera : ℕ) (s : ℂ) (index : ℕ) : ℂ :=
  if camera = 2 then
    centeredBracketExponentSecondDerivTerm s (alignedCenter 2 index) 1
  else
    ∑ radius ∈ radiusSet camera,
      centeredBracketExponentSecondDerivTerm s
        (alignedCenter camera index) radius

/-- Exact derivative of the first exponent derivative of one center block. -/
theorem centerBracketExponentDeriv_hasDerivAt
    {camera : ℕ} (hcamera : 2 ≤ camera) (index : ℕ) (s : ℂ) :
    ComplexAlgebraHasDerivAt
      (fun z => centerBracketExponentDeriv camera z index)
      (centerBracketExponentSecondDeriv camera s index) s := by
  by_cases h2 : camera = 2
  · subst camera
    simp only [centerBracketExponentDeriv,
      centerBracketExponentSecondDeriv, if_pos]
    apply centeredBracketExponentDerivTerm_hasDerivAt
    rw [alignedCenter_eq_cameraSlope_mul, cameraSlope_two]
    omega
  · have hcamera3 : 3 ≤ camera := by omega
    simp only [centerBracketExponentDeriv,
      centerBracketExponentSecondDeriv, h2, if_false]
    exact HasDerivAt.fun_sum fun radius hradius =>
      centeredBracketExponentDerivTerm_hasDerivAt s (by
        have hlower := natural_index_succ_le_alignedCenter_sub hcamera3 hradius
          (index := index)
        omega)

/-- Second exponent derivative of the exceptional seed block. -/
def seedDirichletExponentSecondDeriv (camera : ℕ) (s : ℂ) : ℂ :=
  if camera = 2 then dirichletValueExponentSecondDeriv s 1
  else ∑ radius ∈ radiusSet camera,
    dirichletValueExponentSecondDeriv s radius

/-- Exact derivative of the first exponent derivative of the seed. -/
theorem seedDirichletExponentDeriv_hasDerivAt
    {camera : ℕ} (hcamera : 2 ≤ camera) (s : ℂ) :
    ComplexAlgebraHasDerivAt
      (fun z => seedDirichletExponentDeriv camera z)
      (seedDirichletExponentSecondDeriv camera s) s := by
  by_cases h2 : camera = 2
  · subst camera
    simp only [seedDirichletExponentDeriv,
      seedDirichletExponentSecondDeriv, if_pos]
    exact dirichletValueExponentDeriv_hasDerivAt (by norm_num) s
  · simp only [seedDirichletExponentDeriv,
      seedDirichletExponentSecondDeriv, h2, if_false]
    exact HasDerivAt.fun_sum fun radius hradius =>
      dirichletValueExponentDeriv_hasDerivAt
        ((mem_radiusSet_iff.mp hradius).1.trans_lt' (by omega)) s

/-- Explicit second exponent derivative of the finite characteristic. -/
def finiteBracketCharacteristicExponentSecondDeriv
    (camera cutoff : ℕ) (s : ℂ) : ℂ :=
  seedDirichletExponentSecondDeriv camera s +
    ∑ index ∈ Finset.range cutoff,
      centerBracketExponentSecondDeriv camera s index

/-- The first finite-characteristic exponent derivative has the displayed derivative. -/
theorem finiteBracketCharacteristicExponentDeriv_hasDerivAt
    {camera : ℕ} (hcamera : 2 ≤ camera) (cutoff : ℕ) (s : ℂ) :
    ComplexAlgebraHasDerivAt
      (fun z => finiteBracketCharacteristicExponentDeriv camera cutoff z)
      (finiteBracketCharacteristicExponentSecondDeriv camera cutoff s) s := by
  exact (seedDirichletExponentDeriv_hasDerivAt hcamera s).add
    (HasDerivAt.fun_sum fun index _ =>
      centerBracketExponentDeriv_hasDerivAt hcamera index s)

end

end NativeCarryC3Crosswalk
