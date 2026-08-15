import CPFormal.Analytic.CpGenuineKernelPrimeState
import NativeCarryC3Crosswalk.RealPlaneCameraExtension
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Prime-to-all-bases camera form bridge

This module identifies the finite prime-camera core inside the intrinsic
all-bases Gram core.  The correct prime carrier inherits its norm from that
Gram geometry; it is not the raw unweighted `ℓ²` prime completion.

Every bounded scalar functional on the prime-supported intrinsic core extends
with the same norm to the all-bases camera Hilbert space.  Conversely, Lean
proves a precise obstruction to the naive vector synthesis: no bounded map can
send every orthonormal unweighted prime axis to the raw all-bases camera
vector, whose squared norm is `p * (p - 1)` for every odd prime.

Thus this file closes the typed finite-core inclusion and records exactly why
the research Green/Haar estimate must use the intrinsic Gram norm.  It does
not assert that the enriched Green/Haar formula is bounded in that norm.
-/

open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Infinite

/-- A prime camera regarded as one of the all-bases cameras. -/
def primeCameraIndex (p : Nat.Primes) : CameraIndex :=
  ⟨p.1, p.prop.two_le⟩

/-- The inclusion of prime labels into the all-bases camera index. -/
def primeCameraIndexEmbedding : Nat.Primes ↪ CameraIndex where
  toFun := primeCameraIndex
  inj' := by
    intro p q hpq
    exact Subtype.ext (congrArg (fun c : CameraIndex => (c : ℕ)) hpq)

@[simp] theorem primeCameraIndexEmbedding_apply (p : Nat.Primes) :
    primeCameraIndexEmbedding p = primeCameraIndex p := rfl

/-- Algebraic finite prime-camera coefficients before completion. -/
abbrev PrimeCameraFinsupp := Nat.Primes →₀ ℝ

/-- Exact finite reindexing of prime-camera coefficients into the all-bases
camera core.  This is algebraic and makes no boundedness assertion about the
unweighted completed prime-camera Hilbert space. -/
def primeCameraCoreReindex : PrimeCameraFinsupp →ₗ[ℝ] CameraFinsupp :=
  Finsupp.lmapDomain ℝ ℝ primeCameraIndexEmbedding

@[simp] theorem primeCameraCoreReindex_apply (u : PrimeCameraFinsupp) :
    primeCameraCoreReindex u =
      Finsupp.mapDomain primeCameraIndexEmbedding u := rfl

@[simp] theorem primeCameraCoreReindex_single
    (p : Nat.Primes) (a : ℝ) :
    primeCameraCoreReindex (Finsupp.single p a) =
      Finsupp.single (primeCameraIndex p) a := by
  simp [primeCameraCoreReindex]

theorem primeCameraCoreReindex_injective :
    Function.Injective primeCameraCoreReindex :=
  Finsupp.mapDomain_injective primeCameraIndexEmbedding.injective

/-- The prime-supported core with the intrinsic all-bases Gram norm inherited
from `CameraFinsupp`. -/
def PrimeCameraGramCore : Submodule ℝ CameraFinsupp :=
  LinearMap.range primeCameraCoreReindex

/-- Canonical point of the prime-supported intrinsic Gram core. -/
def primeCameraGramCoreElement
    (u : PrimeCameraFinsupp) : PrimeCameraGramCore :=
  ⟨primeCameraCoreReindex u, ⟨u, rfl⟩⟩

@[simp] theorem primeCameraGramCoreElement_coe
    (u : PrimeCameraFinsupp) :
    (primeCameraGramCoreElement u : CameraFinsupp) =
      primeCameraCoreReindex u := rfl

/-- Hahn--Banach extension from the prime-supported intrinsic Gram core to
the complete finitely supported all-bases core. -/
def extendPrimeCameraGramCoreFunctional
    (q : PrimeCameraGramCore →L[ℝ] ℝ) : CameraCoreFunctional :=
  Classical.choose (exists_extension_norm_eq PrimeCameraGramCore q)

@[simp] theorem extendPrimeCameraGramCoreFunctional_apply
    (q : PrimeCameraGramCore →L[ℝ] ℝ) (u : PrimeCameraGramCore) :
    extendPrimeCameraGramCoreFunctional q u = q u :=
  (Classical.choose_spec
    (exists_extension_norm_eq PrimeCameraGramCore q)).1 u

theorem extendPrimeCameraGramCoreFunctional_norm
    (q : PrimeCameraGramCore →L[ℝ] ℝ) :
    ‖extendPrimeCameraGramCoreFunctional q‖ = ‖q‖ :=
  (Classical.choose_spec
    (exists_extension_norm_eq PrimeCameraGramCore q)).2

/-- The canonical all-bases Hilbert extension of a bounded functional on the
prime-supported intrinsic Gram core. -/
def extendPrimeCameraGramCoreToHilbert
    (q : PrimeCameraGramCore →L[ℝ] ℝ) : CameraHilbertFunctional :=
  extendCameraCoreFunctional (extendPrimeCameraGramCoreFunctional q)

@[simp] theorem extendPrimeCameraGramCoreToHilbert_apply
    (q : PrimeCameraGramCore →L[ℝ] ℝ) (u : PrimeCameraFinsupp) :
    extendPrimeCameraGramCoreToHilbert q
        (cameraEmbedding (primeCameraCoreReindex u)) =
      q (primeCameraGramCoreElement u) := by
  rw [extendPrimeCameraGramCoreToHilbert,
    extendCameraCoreFunctional_cameraEmbedding]
  exact extendPrimeCameraGramCoreFunctional_apply q
    (primeCameraGramCoreElement u)

theorem extendPrimeCameraGramCoreToHilbert_norm
    (q : PrimeCameraGramCore →L[ℝ] ℝ) :
    ‖extendPrimeCameraGramCoreToHilbert q‖ = ‖q‖ := by
  rw [extendPrimeCameraGramCoreToHilbert,
    extendCameraCoreFunctional_norm,
    extendPrimeCameraGramCoreFunctional_norm]

theorem extendPrimeCameraGramCoreToHilbert_bound
    (q : PrimeCameraGramCore →L[ℝ] ℝ) (u : PrimeCameraFinsupp) :
    ‖extendPrimeCameraGramCoreToHilbert q
        (cameraEmbedding (primeCameraCoreReindex u))‖ ≤
      ‖q‖ * ‖primeCameraCoreReindex u‖ := by
  rw [extendPrimeCameraGramCoreToHilbert_apply]
  simpa using q.le_opNorm (primeCameraGramCoreElement u)

/-! ## Native real-plane extension

The native readout has two real coordinates.  Hahn--Banach is applied to
those coordinates and the pair is then reassembled, so no independent
complex channel is introduced.
-/

def primeCameraRealPlaneFirst
    (q : PrimeCameraGramCore →L[ℝ] NativeCarryRealPlane) :
    PrimeCameraGramCore →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp q

def primeCameraRealPlaneSecond
    (q : PrimeCameraGramCore →L[ℝ] NativeCarryRealPlane) :
    PrimeCameraGramCore →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp q

/-- Coordinatewise Hahn--Banach extension of a native real-plane map from the
prime-supported intrinsic core to the full all-bases algebraic core. -/
def extendPrimeCameraGramCoreRealPlaneMap
    (q : PrimeCameraGramCore →L[ℝ] NativeCarryRealPlane) :
    CameraCoreMap (F := NativeCarryRealPlane) :=
  (extendPrimeCameraGramCoreFunctional (primeCameraRealPlaneFirst q)).prod
    (extendPrimeCameraGramCoreFunctional (primeCameraRealPlaneSecond q))

@[simp] theorem extendPrimeCameraGramCoreRealPlaneMap_apply
    (q : PrimeCameraGramCore →L[ℝ] NativeCarryRealPlane)
    (u : PrimeCameraGramCore) :
    extendPrimeCameraGramCoreRealPlaneMap q u = q u := by
  apply Prod.ext
  · exact extendPrimeCameraGramCoreFunctional_apply
      (primeCameraRealPlaneFirst q) u
  · exact extendPrimeCameraGramCoreFunctional_apply
      (primeCameraRealPlaneSecond q) u

private theorem primeCameraRealPlaneFirst_norm_le
    (q : PrimeCameraGramCore →L[ℝ] NativeCarryRealPlane) :
    ‖primeCameraRealPlaneFirst q‖ ≤ ‖q‖ := by
  apply (primeCameraRealPlaneFirst q).opNorm_le_bound (norm_nonneg q)
  intro u
  exact (norm_fst_le (q u)).trans (q.le_opNorm u)

private theorem primeCameraRealPlaneSecond_norm_le
    (q : PrimeCameraGramCore →L[ℝ] NativeCarryRealPlane) :
    ‖primeCameraRealPlaneSecond q‖ ≤ ‖q‖ := by
  apply (primeCameraRealPlaneSecond q).opNorm_le_bound (norm_nonneg q)
  intro u
  exact (norm_snd_le (q u)).trans (q.le_opNorm u)

/-- The coordinatewise extension preserves the exact operator norm of the
native real-plane readout. -/
theorem extendPrimeCameraGramCoreRealPlaneMap_norm
    (q : PrimeCameraGramCore →L[ℝ] NativeCarryRealPlane) :
    ‖extendPrimeCameraGramCoreRealPlaneMap q‖ = ‖q‖ := by
  apply le_antisymm
  · apply (extendPrimeCameraGramCoreRealPlaneMap q).opNorm_le_bound
      (norm_nonneg q)
    intro u
    rw [Prod.norm_def, max_le_iff]
    constructor
    · calc
        ‖extendPrimeCameraGramCoreFunctional
            (primeCameraRealPlaneFirst q) u‖ ≤
            ‖extendPrimeCameraGramCoreFunctional
              (primeCameraRealPlaneFirst q)‖ * ‖u‖ :=
          (extendPrimeCameraGramCoreFunctional
            (primeCameraRealPlaneFirst q)).le_opNorm u
        _ = ‖primeCameraRealPlaneFirst q‖ * ‖u‖ := by
          rw [extendPrimeCameraGramCoreFunctional_norm]
        _ ≤ ‖q‖ * ‖u‖ := mul_le_mul_of_nonneg_right
          (primeCameraRealPlaneFirst_norm_le q) (norm_nonneg u)
    · calc
        ‖extendPrimeCameraGramCoreFunctional
            (primeCameraRealPlaneSecond q) u‖ ≤
            ‖extendPrimeCameraGramCoreFunctional
              (primeCameraRealPlaneSecond q)‖ * ‖u‖ :=
          (extendPrimeCameraGramCoreFunctional
            (primeCameraRealPlaneSecond q)).le_opNorm u
        _ = ‖primeCameraRealPlaneSecond q‖ * ‖u‖ := by
          rw [extendPrimeCameraGramCoreFunctional_norm]
        _ ≤ ‖q‖ * ‖u‖ := mul_le_mul_of_nonneg_right
          (primeCameraRealPlaneSecond_norm_le q) (norm_nonneg u)
  · apply q.opNorm_le_bound
      (norm_nonneg (extendPrimeCameraGramCoreRealPlaneMap q))
    intro u
    rw [← extendPrimeCameraGramCoreRealPlaneMap_apply q u]
    exact (extendPrimeCameraGramCoreRealPlaneMap q).le_opNorm u

/-- Completion of the prime-supported native real-plane map to all cameras. -/
def extendPrimeCameraGramCoreRealPlaneToHilbert
    (q : PrimeCameraGramCore →L[ℝ] NativeCarryRealPlane) :
    CameraHilbertMap (F := NativeCarryRealPlane) :=
  extendCameraCoreMap (extendPrimeCameraGramCoreRealPlaneMap q)

@[simp] theorem extendPrimeCameraGramCoreRealPlaneToHilbert_apply
    (q : PrimeCameraGramCore →L[ℝ] NativeCarryRealPlane)
    (u : PrimeCameraFinsupp) :
    extendPrimeCameraGramCoreRealPlaneToHilbert q
        (cameraEmbedding (primeCameraCoreReindex u)) =
      q (primeCameraGramCoreElement u) := by
  rw [extendPrimeCameraGramCoreRealPlaneToHilbert,
    extendCameraCoreMap_cameraEmbedding]
  exact extendPrimeCameraGramCoreRealPlaneMap_apply q
    (primeCameraGramCoreElement u)

theorem extendPrimeCameraGramCoreRealPlaneToHilbert_norm
    (q : PrimeCameraGramCore →L[ℝ] NativeCarryRealPlane) :
    ‖extendPrimeCameraGramCoreRealPlaneToHilbert q‖ = ‖q‖ := by
  rw [extendPrimeCameraGramCoreRealPlaneToHilbert,
    extendCameraCoreMap_norm,
    extendPrimeCameraGramCoreRealPlaneMap_norm]

private theorem sum_dvdIndicator_range (camera : ℕ) (hcamera : 0 < camera) :
    ∑ n ∈ Finset.range camera, dvdIndicator camera n = 1 := by
  calc
    ∑ n ∈ Finset.range camera, dvdIndicator camera n =
        dvdIndicator camera 0 := by
      apply Finset.sum_eq_single 0
      · intro n hn hn0
        have hnlt : n < camera := Finset.mem_range.mp hn
        have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        simp [dvdIndicator, Nat.not_dvd_of_pos_of_lt hnpos hnlt]
      · intro hzero
        exact False.elim (hzero (Finset.mem_range.mpr hcamera))
    _ = 1 := by simp [dvdIndicator]

private theorem oddProfile_square_sum_range
    (camera : ℕ) (hcamera : 0 < camera) :
    ∑ n ∈ Finset.range camera,
        oddProfile camera n * oddProfile camera n =
      (camera : ℤ) * ((camera : ℤ) - 1) := by
  have hpoint : ∀ n : ℕ,
      oddProfile camera n * oddProfile camera n =
        1 + (((camera : ℤ) ^ 2 - 2 * (camera : ℤ)) *
          dvdIndicator camera n) := by
    intro n
    simp only [oddProfile, dvdIndicator]
    split <;> ring
  simp_rw [hpoint, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, sum_dvdIndicator_range camera hcamera]
  simp
  ring

private theorem periodicProductSum_prime_self
    (p : Nat.Primes) (hp2 : (p : ℕ) ≠ 2) :
    periodicProductSum p p p =
      (p : ℤ) * ((p : ℤ) - 1) := by
  have hodd : Odd (p : ℕ) := p.prop.odd_of_ne_two hp2
  rw [periodicProductSum]
  simp_rw [profile_of_odd hp2 hodd]
  exact oddProfile_square_sum_range p p.prop.pos

theorem gramKernel_primeCameraIndex_self
    (p : Nat.Primes) (hp2 : (p : ℕ) ≠ 2) :
    gramKernel (primeCameraIndex p) (primeCameraIndex p) =
      (p : ℝ) * ((p : ℝ) - 1) := by
  have hslope : cameraSlope (p : ℕ) = p := cameraSlope_of_ne_two hp2
  simp only [gramKernel, periodicMeanKernel, pairPeriod,
    primeCameraIndex, cameraLabel]
  rw [hslope, Nat.min_self, Nat.lcm_self, periodicProductMean,
    periodicProductSum_prime_self p hp2]
  norm_cast
  field_simp [p.prop.ne_zero]

theorem norm_cameraVector_prime_sq
    (p : Nat.Primes) (hp2 : (p : ℕ) ≠ 2) :
    ‖cameraVector (primeCameraIndex p)‖ ^ 2 =
      (p : ℝ) * ((p : ℝ) - 1) := by
  rw [norm_cameraVector_sq, gramKernel_primeCameraIndex_self p hp2]

/-- There is no bounded linear synthesis sending the orthonormal unweighted
prime axes to the raw all-bases camera vectors.  The latter have squared norm
`p * (p - 1)`, so the required operator norm would be unbounded. -/
theorem no_bounded_rawPrimeCameraAxis_synthesis :
    ¬ ∃ T : PrimeGreenCameraHilbert →L[ℝ] CameraHilbert,
      ∀ p : Nat.Primes,
        T (primeGreenCameraAxis p) = cameraVector (primeCameraIndex p) := by
  rintro ⟨T, hT⟩
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (‖T‖ ^ 2)
  obtain ⟨p : ℕ, hpLower, hpPrime⟩ :=
    Nat.exists_infinite_primes (max n 3)
  let p' : Nat.Primes := ⟨p, hpPrime⟩
  have hp3 : 3 ≤ p := le_trans (le_max_right n 3) hpLower
  have hp2 : p ≠ 2 := by omega
  have haxisNorm : ‖primeGreenCameraAxis p'‖ = 1 := by
    rw [primeGreenCameraAxis,
      lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
    norm_num
  have hbound : ‖cameraVector (primeCameraIndex p')‖ ≤ ‖T‖ := by
    have hop := T.le_opNorm (primeGreenCameraAxis p')
    rw [hT p', haxisNorm, mul_one] at hop
    exact hop
  have hnle : n ≤ p := le_trans (le_max_left n 3) hpLower
  have hnorm_lt_p : ‖T‖ ^ 2 < (p : ℝ) :=
    lt_of_lt_of_le hn (by exact_mod_cast hnle)
  have hp_le_product : (p : ℝ) ≤ (p : ℝ) * ((p : ℝ) - 1) := by
    have hp3real : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp3
    nlinarith
  have htarget : ‖T‖ ^ 2 <
      ‖cameraVector (primeCameraIndex p')‖ ^ 2 := by
    rw [norm_cameraVector_prime_sq p' hp2]
    exact lt_of_lt_of_le hnorm_lt_p hp_le_product
  have hsquares : ‖cameraVector (primeCameraIndex p')‖ ^ 2 ≤ ‖T‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg (cameraVector (primeCameraIndex p')))
      (norm_nonneg T)).2 hbound
  exact (not_lt_of_ge hsquares) htarget

end NativeCarryC3Crosswalk
