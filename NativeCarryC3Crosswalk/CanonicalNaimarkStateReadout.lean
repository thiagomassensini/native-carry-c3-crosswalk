import NativeCarrySpectralWeyl.Infinite.ComplexifiedResolvent

/-!
# Canonical camera readout from an ambient Naimark realization

The finite formula `R = (C C*)⁻¹ᐟ² C` has a coordinate-free analogue.  The
intrinsic camera completion embeds isometrically into the Naimark space; its
adjoint is therefore the canonical coisometric readout.

Consequently a state-to-camera map needs no additional choice once a bounded
state realization in the Naimark ambient space is known:

`stateReadout = realifiedNaimarkAdjoint ∘ stateRealization`.

This module proves the exact left-inverse law and the factorization theorem.
It deliberately does not postulate the research-specific realization of the
complete C3/TFVD port; that is the remaining analytic datum.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace NativeCarryC3Crosswalk

open NativeCarrySpectralWeyl.Infinite

/-- The all-bases Naimark adjoint is a left inverse of the Naimark isometry. -/
theorem naimarkAdjoint_comp_naimarkIsometry :
    naimarkAdjoint ∘L naimarkIsometry.toContinuousLinearMap = 1 := by
  exact naimarkIsometry.adjoint_comp_self

/-- Coordinatewise realification retains the same exact left-inverse law. -/
theorem realifiedNaimarkAdjoint_comp_realifiedNaimarkPort :
    realifiedNaimarkAdjoint ∘L realifiedNaimarkPort = 1 := by
  have hleft (x : CameraHilbert) :
      naimarkAdjoint (naimarkIsometry.toContinuousLinearMap x) = x := by
    have h := congrArg
      (fun T : CameraHilbert →L[ℝ] CameraHilbert ↦ T x)
      naimarkAdjoint_comp_naimarkIsometry
    simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self] using h
  apply ContinuousLinearMap.ext
  intro u
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · simp [ContinuousLinearMap.comp_apply, realifiedNaimarkAdjoint,
      realifiedNaimarkPort]
    simpa only [LinearIsometry.coe_toContinuousLinearMap] using hleft u.fst
  · simp [ContinuousLinearMap.comp_apply, realifiedNaimarkAdjoint,
      realifiedNaimarkPort]
    simpa only [LinearIsometry.coe_toContinuousLinearMap] using hleft u.snd

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Canonical camera compression of a bounded ambient state realization. -/
def canonicalCameraStateReadout
    (stateRealization : H →L[ℝ] RealifiedNaimarkComplexification) :
    H →L[ℝ] RealifiedCameraComplexification :=
  realifiedNaimarkAdjoint ∘L stateRealization

@[simp] theorem canonicalCameraStateReadout_apply
    (stateRealization : H →L[ℝ] RealifiedNaimarkComplexification) (x : H) :
    canonicalCameraStateReadout stateRealization x =
      realifiedNaimarkAdjoint (stateRealization x) :=
  rfl

@[simp] theorem canonicalCameraStateReadout_fst
    (stateRealization : H →L[ℝ] RealifiedNaimarkComplexification) (x : H) :
    (canonicalCameraStateReadout stateRealization x).fst =
      naimarkAdjoint (stateRealization x).fst := by
  simp [canonicalCameraStateReadout, ContinuousLinearMap.comp_apply]

@[simp] theorem canonicalCameraStateReadout_snd
    (stateRealization : H →L[ℝ] RealifiedNaimarkComplexification) (x : H) :
    (canonicalCameraStateReadout stateRealization x).snd =
      naimarkAdjoint (stateRealization x).snd := by
  simp [canonicalCameraStateReadout, ContinuousLinearMap.comp_apply]

/-- Riesz/Green spelling of the first real coordinate: testing the canonical
readout against an intrinsic camera vector is exactly testing the ambient
state against the corresponding Naimark vector. -/
theorem inner_canonicalCameraStateReadout_fst
    (stateRealization : H →L[ℝ] RealifiedNaimarkComplexification)
    (u : CameraHilbert) (x : H) :
    inner ℝ u (canonicalCameraStateReadout stateRealization x).fst =
      inner ℝ (naimarkIsometry u) (stateRealization x).fst := by
  rw [canonicalCameraStateReadout_fst]
  simpa [naimarkAdjoint] using
    naimarkIsometry.toContinuousLinearMap.adjoint_inner_right u
      (stateRealization x).fst

/-- The same ambient/intrinsic pairing identity for the second real
coordinate. -/
theorem inner_canonicalCameraStateReadout_snd
    (stateRealization : H →L[ℝ] RealifiedNaimarkComplexification)
    (u : CameraHilbert) (x : H) :
    inner ℝ u (canonicalCameraStateReadout stateRealization x).snd =
      inner ℝ (naimarkIsometry u) (stateRealization x).snd := by
  rw [canonicalCameraStateReadout_snd]
  simpa [naimarkAdjoint] using
    naimarkIsometry.toContinuousLinearMap.adjoint_inner_right u
      (stateRealization x).snd

/-- If the state realization is already coherent camera data inserted by the
Naimark port, canonical compression recovers that data exactly. -/
theorem canonicalCameraStateReadout_of_coherent
    (q : H →L[ℝ] RealifiedCameraComplexification) :
    canonicalCameraStateReadout (realifiedNaimarkPort ∘L q) = q := by
  rw [canonicalCameraStateReadout, ← ContinuousLinearMap.comp_assoc,
    realifiedNaimarkAdjoint_comp_realifiedNaimarkPort]
  ext x
  rfl

/-- Pointwise form of the exact coherent reconstruction law. -/
@[simp] theorem canonicalCameraStateReadout_coherent_apply
    (q : H →L[ℝ] RealifiedCameraComplexification) (x : H) :
    canonicalCameraStateReadout (realifiedNaimarkPort ∘L q) x = q x := by
  rw [canonicalCameraStateReadout_of_coherent q]

end NativeCarryC3Crosswalk
