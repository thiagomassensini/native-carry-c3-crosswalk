import NativeCarrySpectralWeyl.Boundary.GammaField

/-!
# Realified gamma Green energy

The source-parametrized carry gamma field is built on the canonical real
two-channel complexification.  Applying the already established source
relation Green identity to its two coordinates gives the exact diagonal
energy law

`CauchySkew(lambda,u) = -lambda.im * GammaEnergy(lambda,u)`.

This is an operator-theoretic identity.  It does not identify the Cauchy
boundary pair with the completed Genuine value/log-jet pair; that
scalarization remains a separate analytic obligation.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace NativeCarryC3Crosswalk

open NativeCarrySpectralWeyl.Infinite
open NativeCarrySpectralWeyl.Boundary

/-- The two real components of a source-parametrized defect vector satisfy
the cross Green identity inherited from the source-extended relation. -/
theorem carryGammaSource_cross_green_identity
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (u : RealifiedCameraComplexification) :
    greenForm (𝕜 := ℝ)
        ((carryGammaSource lambda hlambda u).fst,
          lambda.re • (carryGammaSource lambda hlambda u).fst -
            lambda.im • (carryGammaSource lambda hlambda u).snd)
        ((carryGammaSource lambda hlambda u).snd,
          lambda.im • (carryGammaSource lambda hlambda u).fst +
            lambda.re • (carryGammaSource lambda hlambda u).snd) =
      greenForm (𝕜 := ℝ)
        (naimarkAdjoint (carryGammaSource lambda hlambda u).fst, u.fst)
        (naimarkAdjoint (carryGammaSource lambda hlambda u).snd, u.snd) := by
  have hfst :
      lambda.re • (carryGammaSource lambda hlambda u).fst -
          lambda.im • (carryGammaSource lambda hlambda u).snd =
        logarithmicMultiplication
            (carryGammaIntoDomain lambda hlambda u).1 +
          naimarkIsometry u.fst := by
    have h := congrArg WithLp.fst
      (carryGammaSource_defect_equation lambda hlambda u)
    simpa only [realifiedNaimarkScalar_fst, WithLp.add_fst,
      realifiedLogarithmicMultiplication_fst,
      realifiedNaimarkPort_fst] using h

  have hsnd :
      lambda.im • (carryGammaSource lambda hlambda u).fst +
          lambda.re • (carryGammaSource lambda hlambda u).snd =
        logarithmicMultiplication
            (carryGammaIntoDomain lambda hlambda u).2 +
          naimarkIsometry u.snd := by
    have h := congrArg WithLp.snd
      (carryGammaSource_defect_equation lambda hlambda u)
    simpa only [realifiedNaimarkScalar_snd, WithLp.add_snd,
      realifiedLogarithmicMultiplication_snd,
      realifiedNaimarkPort_snd] using h

  have hgreen :=
    carrySourceRelation_weyl_green_identity
      (carrySourceRelationElement
        (carryGammaIntoDomain lambda hlambda u).1 u.fst)
      (carrySourceRelationElement
        (carryGammaIntoDomain lambda hlambda u).2 u.snd)

  simp only [coe_carrySourceRelationElement,
    carryWeylBoundaryMap_element,
    carryGammaIntoDomain_fst_coe,
    carryGammaIntoDomain_snd_coe] at hgreen
  rw [← hfst, ← hsnd] at hgreen
  exact hgreen

/-- The Cauchy boundary skew is exactly minus the imaginary spectral
parameter times the realified gamma energy. -/
theorem carryGammaSource_cauchy_skew_energy
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (u : RealifiedCameraComplexification) :
    inner ℝ u.fst (allBasesCauchyBlock lambda hlambda u).snd -
        inner ℝ u.snd (allBasesCauchyBlock lambda hlambda u).fst =
      -lambda.im *
        (‖(carryGammaSource lambda hlambda u).fst‖ ^ 2 +
          ‖(carryGammaSource lambda hlambda u).snd‖ ^ 2) := by
  have hinterior :
      greenForm (𝕜 := ℝ)
          ((carryGammaSource lambda hlambda u).fst,
            lambda.re • (carryGammaSource lambda hlambda u).fst -
              lambda.im • (carryGammaSource lambda hlambda u).snd)
          ((carryGammaSource lambda hlambda u).snd,
            lambda.im • (carryGammaSource lambda hlambda u).fst +
              lambda.re • (carryGammaSource lambda hlambda u).snd) =
        -lambda.im *
          (‖(carryGammaSource lambda hlambda u).fst‖ ^ 2 +
            ‖(carryGammaSource lambda hlambda u).snd‖ ^ 2) := by
    simp only [greenForm, inner_sub_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    ring

  have hadjoint :
      inner ℝ u.fst
          (naimarkAdjoint (carryGammaSource lambda hlambda u).snd) -
        inner ℝ u.snd
          (naimarkAdjoint (carryGammaSource lambda hlambda u).fst) =
      -lambda.im *
        (‖(carryGammaSource lambda hlambda u).fst‖ ^ 2 +
          ‖(carryGammaSource lambda hlambda u).snd‖ ^ 2) := by
    rw [real_inner_comm
      (naimarkAdjoint (carryGammaSource lambda hlambda u).fst) u.snd]
    calc
      inner ℝ u.fst
            (naimarkAdjoint (carryGammaSource lambda hlambda u).snd) -
          inner ℝ
            (naimarkAdjoint (carryGammaSource lambda hlambda u).fst)
            u.snd =
          greenForm (𝕜 := ℝ)
            (naimarkAdjoint
                (carryGammaSource lambda hlambda u).fst, u.fst)
            (naimarkAdjoint
                (carryGammaSource lambda hlambda u).snd, u.snd) := rfl
      _ = greenForm (𝕜 := ℝ)
            ((carryGammaSource lambda hlambda u).fst,
              lambda.re • (carryGammaSource lambda hlambda u).fst -
                lambda.im • (carryGammaSource lambda hlambda u).snd)
            ((carryGammaSource lambda hlambda u).snd,
              lambda.im • (carryGammaSource lambda hlambda u).fst +
                lambda.re •
                  (carryGammaSource lambda hlambda u).snd) :=
        (carryGammaSource_cross_green_identity
          lambda hlambda u).symm
      _ = _ := hinterior

  have hcauchy :
      realifiedNaimarkAdjoint (carryGammaSource lambda hlambda u) =
        allBasesCauchyBlock lambda hlambda u := by
    simpa only [carryDefectGammaZero,
      ContinuousLinearMap.comp_apply] using
      (carryDefectGammaZero_apply lambda hlambda u)

  have hcfst := congrArg WithLp.fst hcauchy
  have hcsnd := congrArg WithLp.snd hcauchy
  simp only [realifiedNaimarkAdjoint_fst] at hcfst
  simp only [realifiedNaimarkAdjoint_snd] at hcsnd

  rw [← hcsnd, ← hcfst]
  exact hadjoint

/-- Antisymmetrizing the two real boundary channels produces the factor-two
diagonal Green identity. -/
theorem carryGammaSource_diagonal_green_identity
    (lambda : ℂ) (hlambda : lambda.im ≠ 0)
    (u : RealifiedCameraComplexification) :
    2 * lambda.im *
        (‖(carryGammaSource lambda hlambda u).fst‖ ^ 2 +
          ‖(carryGammaSource lambda hlambda u).snd‖ ^ 2) =
      greenForm (𝕜 := ℝ)
          ((allBasesCauchyBlock lambda hlambda u).snd, u.snd)
          ((allBasesCauchyBlock lambda hlambda u).fst, u.fst) -
        greenForm (𝕜 := ℝ)
          ((allBasesCauchyBlock lambda hlambda u).fst, u.fst)
          ((allBasesCauchyBlock lambda hlambda u).snd, u.snd) := by
  have hskew :=
    carryGammaSource_cauchy_skew_energy lambda hlambda u
  calc
    2 * lambda.im *
          (‖(carryGammaSource lambda hlambda u).fst‖ ^ 2 +
            ‖(carryGammaSource lambda hlambda u).snd‖ ^ 2) =
        -2 *
          (inner ℝ u.fst
              (allBasesCauchyBlock lambda hlambda u).snd -
            inner ℝ u.snd
              (allBasesCauchyBlock lambda hlambda u).fst) := by
      rw [hskew]
      ring
    _ = greenForm (𝕜 := ℝ)
          ((allBasesCauchyBlock lambda hlambda u).snd, u.snd)
          ((allBasesCauchyBlock lambda hlambda u).fst, u.fst) -
        greenForm (𝕜 := ℝ)
          ((allBasesCauchyBlock lambda hlambda u).fst, u.fst)
          ((allBasesCauchyBlock lambda hlambda u).snd, u.snd) := by
      simp only [greenForm]
      rw [real_inner_comm
          (allBasesCauchyBlock lambda hlambda u).snd u.fst,
        real_inner_comm
          (allBasesCauchyBlock lambda hlambda u).fst u.snd]
      ring

end NativeCarryC3Crosswalk
