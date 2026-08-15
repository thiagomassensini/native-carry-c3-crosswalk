import CPFormal.Analytic.CpNativeCarryComplexOperatorSameAsReal
import NativeCarrySpectralWeyl.Boundary.GreenHaarCameraForm

/-!
# Real-plane all-bases camera extension

The native operator is defined in the real plane.  Its complex notation is
already proved upstream to be the inverse-coordinate packaging through
`Complex.equivRealProdCLM`; it is not another operator or another channel.

This module proves that the all-bases dense-core extension respects that
existing identification.  Extending a real-plane camera map and then
packaging it is exactly the same as packaging the core map and then extending
it.  Consequently, packaging neither creates nor removes zeros and preserves
the native quadratic energy after completion.

No zero, critical-line, tilt, isotropy, or confinement hypothesis is used.
-/

open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Infinite

/-- Package a real-plane camera-core map in the equivalent complex
coordinates. -/
def packageRealPlaneCameraCoreMap
    (q : CameraCoreMap (F := NativeCarryRealPlane)) :
    CameraCoreMap (F := ℂ) :=
  Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp q

/-- Package a real-plane all-bases map in the equivalent complex
coordinates. -/
def packageRealPlaneCameraHilbertMap
    (Q : CameraHilbertMap (F := NativeCarryRealPlane)) :
    CameraHilbertMap (F := ℂ) :=
  Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp Q

@[simp] theorem packageRealPlaneCameraCoreMap_apply
    (q : CameraCoreMap (F := NativeCarryRealPlane))
    (u : CameraFinsupp) :
    packageRealPlaneCameraCoreMap q u =
      nativeCarryRealPlaneComplexPackaging (q u) := by
  rw [packageRealPlaneCameraCoreMap]
  exact congrFun
    nativeCarryRealPlaneComplexPackaging_eq_equivRealProdCLM_symm
      (q u) |>.symm

@[simp] theorem packageRealPlaneCameraHilbertMap_apply
    (Q : CameraHilbertMap (F := NativeCarryRealPlane))
    (u : CameraHilbert) :
    packageRealPlaneCameraHilbertMap Q u =
      nativeCarryRealPlaneComplexPackaging (Q u) := by
  rw [packageRealPlaneCameraHilbertMap]
  exact congrFun
    nativeCarryRealPlaneComplexPackaging_eq_equivRealProdCLM_symm
      (Q u) |>.symm

/-- Dense-core extension commutes exactly with the already-proved coordinate
equivalence between the native real plane and its complex packaging. -/
theorem extend_packageRealPlaneCameraCoreMap
    (q : CameraCoreMap (F := NativeCarryRealPlane)) :
    extendCameraCoreMap (packageRealPlaneCameraCoreMap q) =
      packageRealPlaneCameraHilbertMap (extendCameraCoreMap q) := by
  symm
  apply extendCameraCoreMap_unique
  intro u
  rw [packageRealPlaneCameraHilbertMap_apply,
    packageRealPlaneCameraCoreMap_apply,
    extendCameraCoreMap_cameraEmbedding]

/-- Complex-coordinate vanishing after extension is exactly real-plane
vanishing; packaging neither creates nor removes an atlas zero. -/
theorem packageRealPlane_extended_eq_zero_iff
    (q : CameraCoreMap (F := NativeCarryRealPlane))
    (u : CameraHilbert) :
    packageRealPlaneCameraHilbertMap (extendCameraCoreMap q) u = 0 ↔
      extendCameraCoreMap q u = 0 := by
  rw [packageRealPlaneCameraHilbertMap_apply]
  constructor
  · intro h
    apply nativeCarryRealPlaneComplexPackaging_injective
    simpa using h
  · intro h
    simp [h]

/-- The packaged extension has exactly the native real quadratic energy. -/
theorem normSq_packageRealPlane_extended_eq_realEnergy
    (q : CameraCoreMap (F := NativeCarryRealPlane))
    (u : CameraHilbert) :
    Complex.normSq
        (packageRealPlaneCameraHilbertMap (extendCameraCoreMap q) u) =
      nativeCarryRealPlaneEnergy (extendCameraCoreMap q u) := by
  rw [packageRealPlaneCameraHilbertMap_apply]
  exact normSq_nativeCarryRealPlaneComplexPackaging _

end NativeCarryC3Crosswalk
