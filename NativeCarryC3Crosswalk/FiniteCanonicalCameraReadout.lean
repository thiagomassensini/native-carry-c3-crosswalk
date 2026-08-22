import NativeCarrySpectralWeyl.Finite.Whitening

/-!
# Canonical finite camera readout

This file isolates the exact linear-algebraic operation used by the finite
native-carry laboratories.  Given a real camera matrix `C`, its row Gram is

`G = C * Cᵀ`.

When `G` is positive definite, the canonical readout and synthesis are

`R = G⁻¹ᐟ² * C`,  `V = Cᵀ * G⁻¹ᐟ²`.

They are transposes of one another and satisfy `R * V = 1`.  Thus `R` is a
coisometry and `V` is an isometry.  No calibration matrix or selected inverse
is introduced: the positive inverse square root is the unique CFC branch
already used by the spectral package.
-/

open scoped Matrix

noncomputable section

namespace NativeCarryC3Crosswalk

open NativeCarrySpectralWeyl.Finite

variable {camera state : Type*}
  [Fintype camera] [DecidableEq camera]
  [Fintype state]

/-- Row Gram of a finite real camera matrix. -/
def finiteCameraRowGram (C : Matrix camera state ℝ) :
    Matrix camera camera ℝ :=
  C * Cᵀ

/-- Canonically whitened finite camera readout. -/
def finiteCanonicalCameraReadout (C : Matrix camera state ℝ) :
    Matrix camera state ℝ :=
  positiveInverseSqrt (finiteCameraRowGram C) * C

/-- Transposed canonical synthesis associated with the finite readout. -/
def finiteCanonicalCameraSynthesis (C : Matrix camera state ℝ) :
    Matrix state camera ℝ :=
  Cᵀ * positiveInverseSqrt (finiteCameraRowGram C)

/-- The canonical readout and synthesis are literal transposes. -/
theorem finiteCanonicalCameraReadout_transpose
    {C : Matrix camera state ℝ}
    (hG : (finiteCameraRowGram C).PosDef) :
    (finiteCanonicalCameraReadout C)ᵀ =
      finiteCanonicalCameraSynthesis C := by
  rw [finiteCanonicalCameraReadout, finiteCanonicalCameraSynthesis,
    Matrix.transpose_mul]
  have hR := positiveInverseSqrt_isHermitian hG
  have hRT : (positiveInverseSqrt (finiteCameraRowGram C))ᵀ =
      positiveInverseSqrt (finiteCameraRowGram C) := by
    ext i j
    simpa only [Matrix.transpose_apply, Matrix.conjTranspose_apply,
      star_trivial] using congr_fun (congr_fun hR.eq i) j
  rw [hRT]

/-- Exact coisometry identity `R Rᵀ = I`. -/
theorem finiteCanonicalCameraReadout_mul_transpose
    {C : Matrix camera state ℝ}
    (hG : (finiteCameraRowGram C).PosDef) :
    finiteCanonicalCameraReadout C *
        (finiteCanonicalCameraReadout C)ᵀ = 1 := by
  rw [finiteCanonicalCameraReadout_transpose hG]
  unfold finiteCanonicalCameraReadout finiteCanonicalCameraSynthesis
    finiteCameraRowGram
  have hwhite := positiveInverseSqrt_whitens hG
  calc
    (positiveInverseSqrt (C * Cᵀ) * C) *
        (Cᵀ * positiveInverseSqrt (C * Cᵀ)) =
      positiveInverseSqrt (C * Cᵀ) * (C * Cᵀ) *
        positiveInverseSqrt (C * Cᵀ) := by
          simp only [Matrix.mul_assoc]
    _ = 1 := hwhite

/-- Exact isometry identity `Vᵀ V = I`. -/
theorem finiteCanonicalCameraSynthesis_transpose_mul
    {C : Matrix camera state ℝ}
    (hG : (finiteCameraRowGram C).PosDef) :
    (finiteCanonicalCameraSynthesis C)ᵀ *
        finiteCanonicalCameraSynthesis C = 1 := by
  rw [← finiteCanonicalCameraReadout_transpose hG,
    Matrix.transpose_transpose]
  exact finiteCanonicalCameraReadout_mul_transpose hG

/-- Readout followed by synthesis is the identity on finite camera data. -/
theorem finiteCanonicalCameraReadout_synthesis
    {C : Matrix camera state ℝ}
    (hG : (finiteCameraRowGram C).PosDef) :
    finiteCanonicalCameraReadout C *
        finiteCanonicalCameraSynthesis C = 1 := by
  rw [← finiteCanonicalCameraReadout_transpose hG]
  exact finiteCanonicalCameraReadout_mul_transpose hG

end NativeCarryC3Crosswalk

