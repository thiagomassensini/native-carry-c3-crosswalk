import NativeCarrySpectralWeyl.Limits.FiniteDefectCovariance

/-!
# Exact cutoff decomposition of the literal camera Gram

The limiting all-bases Gram is not inserted after the finite calculation.
The literal native coefficients split exactly into

* a periodic core of length `min(ell_b, ell_c) * M`;
* a boundary correction whose width is independent of `M`.

Centering the core by its period mean gives the exact identity

`<C_b,M,C_c,M> = M * G(b,c) + E_b,c(M)`.

This is an equality at every cutoff.  It identifies the finite residue that
the numerical laboratory sees and shows where the `1/M` normalized error
comes from.  Periodicity and a uniform bound for this explicit residue are
separate refinements; no asymptotic remainder is hidden in the definition.
-/

open scoped BigOperators
open Filter

noncomputable section

namespace NativeCarryC3Crosswalk

open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Finite
open NativeCarrySpectralWeyl.Limits

/-- Unnormalized row Gram of two literal finite native-camera stencils. -/
def literalFiniteCameraGram
    (cutoff camera₁ camera₂ : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (pairFiniteWindow camera₁ camera₂ cutoff),
    finiteCoefficientAt camera₁ cutoff n *
      finiteCoefficientAt camera₂ cutoff n

/-- The exact centered-core plus finite-boundary residue at one cutoff. -/
def exactCutoffCameraGramResidue
    (period cutoff camera₁ camera₂ : ℕ) : ℝ :=
  (∑ n ∈ Finset.range (pairCoreLength camera₁ camera₂ cutoff),
    (realProfileProduct camera₁ camera₂ (n + 1) -
      periodicProductMean period camera₁ camera₂)) +
    finiteBoundarySum (fun _ ↦ 1) cutoff camera₁ camera₂

/-- Every literal cutoff Gram is exactly its linear periodic-Gram term plus
the explicit centered core and boundary residue. -/
theorem literalFiniteCameraGram_eq_linear_add_residue
    {period cutoff camera₁ camera₂ : ℕ}
    (hcamera₁ : 2 ≤ camera₁) (hcamera₂ : 2 ≤ camera₂) :
    literalFiniteCameraGram cutoff camera₁ camera₂ =
      (cutoff : ℝ) *
          ((min (cameraSlope camera₁) (cameraSlope camera₂) : ℕ) *
            periodicProductMean period camera₁ camera₂) +
        exactCutoffCameraGramResidue period cutoff camera₁ camera₂ := by
  have hsplit :=
    finiteCoefficientWeightedSum_eq_shiftedCore_add_boundary
      (weight := fun _ ↦ (1 : ℝ)) (cutoff := cutoff)
      (camera₁ := camera₁) (camera₂ := camera₂) hcamera₁ hcamera₂
  simp only [one_mul] at hsplit
  rw [literalFiniteCameraGram, hsplit, exactCutoffCameraGramResidue,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
  simp only [nsmul_eq_mul, Nat.cast_mul, pairCoreLength]
  ring

/-- Matrix-entry spelling: when `period` is common to a finite camera
family, the linear term is exactly its established periodic Gram matrix. -/
theorem literalFiniteCameraGram_eq_periodicGram_add_residue
    {index : Type*} [Fintype index]
    {period cutoff : ℕ} {camera : index → ℕ}
    (hcamera : ∀ i, 2 ≤ camera i) (i j : index) :
    literalFiniteCameraGram cutoff (camera i) (camera j) =
      (cutoff : ℝ) * periodicGramMatrix period camera i j +
        exactCutoffCameraGramResidue period cutoff (camera i) (camera j) := by
  rw [literalFiniteCameraGram_eq_linear_add_residue
    (hcamera i) (hcamera j), periodicGramMatrix_apply]

/-- Dividing by a positive cutoff leaves exactly one explicit `1/M`
correction and no further analytic remainder. -/
theorem normalizedLiteralFiniteCameraGram_eq_periodicGram_add_residue_div
    {index : Type*} [Fintype index]
    {period cutoff : ℕ} {camera : index → ℕ}
    (hcutoff : 0 < cutoff) (hcamera : ∀ i, 2 ≤ camera i) (i j : index) :
    (cutoff : ℝ)⁻¹ *
        literalFiniteCameraGram cutoff (camera i) (camera j) =
      periodicGramMatrix period camera i j +
        (cutoff : ℝ)⁻¹ *
          exactCutoffCameraGramResidue period cutoff (camera i) (camera j) := by
  rw [literalFiniteCameraGram_eq_periodicGram_add_residue hcamera i j]
  have hcutoffReal : (cutoff : ℝ) ≠ 0 := by positivity
  field_simp

/-! ## Exact cutoff-to-completion passage -/

/-- The unweighted finite boundary correction is uniformly bounded in the
cutoff.  The bound is deliberately elementary: fixed boundary width times
the two uniform coefficient bounds. -/
theorem norm_finiteBoundarySum_one_le
    {cutoff camera₁ camera₂ : ℕ}
    (hcamera₁ : 2 ≤ camera₁) (hcamera₂ : 2 ≤ camera₂) :
    ‖finiteBoundarySum (fun _ ↦ (1 : ℝ)) cutoff camera₁ camera₂‖ ≤
      (pairBoundaryWidth camera₁ camera₂ : ℝ) *
        ((camera₁ + 4 : ℕ) : ℝ) * ((camera₂ + 4 : ℕ) : ℝ) := by
  unfold finiteBoundarySum
  calc
    ‖∑ r ∈ Finset.range (pairBoundaryWidth camera₁ camera₂),
        finiteBoundaryTerm (fun _ ↦ (1 : ℝ)) cutoff camera₁ camera₂ r‖ ≤
      ∑ r ∈ Finset.range (pairBoundaryWidth camera₁ camera₂),
        ‖finiteBoundaryTerm (fun _ ↦ (1 : ℝ)) cutoff camera₁ camera₂ r‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _r ∈ Finset.range (pairBoundaryWidth camera₁ camera₂),
        (((camera₁ + 4 : ℕ) : ℝ) * ((camera₂ + 4 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro r hr
      rw [finiteBoundaryTerm]
      split_ifs
      · simp only [one_mul, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul
          (abs_finiteCoefficientAt_le hcamera₁)
          (abs_finiteCoefficientAt_le hcamera₂)
          (abs_nonneg _) (by positivity)
      · simp only [norm_zero]
        positivity
    _ = (pairBoundaryWidth camera₁ camera₂ : ℝ) *
        ((camera₁ + 4 : ℕ) : ℝ) * ((camera₂ + 4 : ℕ) : ℝ) := by
      simp [mul_assoc]

/-- Consequently the normalized literal boundary correction vanishes. -/
theorem tendsto_inv_mul_finiteBoundarySum_one_zero
    {camera₁ camera₂ : ℕ}
    (hcamera₁ : 2 ≤ camera₁) (hcamera₂ : 2 ≤ camera₂) :
    Tendsto (fun cutoff : ℕ ↦
      (cutoff : ℝ)⁻¹ *
        finiteBoundarySum (fun _ ↦ (1 : ℝ)) cutoff camera₁ camera₂)
      atTop (nhds 0) := by
  have hbounded : IsBoundedUnder (· ≤ ·) atTop
      (norm ∘ fun cutoff : ℕ ↦
        finiteBoundarySum (fun _ ↦ (1 : ℝ)) cutoff camera₁ camera₂) := by
    change ∃ bound : ℝ, ∀ᶠ cutoff : ℕ in atTop,
      ‖finiteBoundarySum (fun _ ↦ (1 : ℝ)) cutoff camera₁ camera₂‖ ≤ bound
    exact ⟨(pairBoundaryWidth camera₁ camera₂ : ℝ) *
        ((camera₁ + 4 : ℕ) : ℝ) * ((camera₂ + 4 : ℕ) : ℝ),
      Filter.Eventually.of_forall fun cutoff ↦
        norm_finiteBoundarySum_one_le hcamera₁ hcamera₂⟩
  have hzero :=
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).zero_smul_isBoundedUnder_le
      hbounded
  simpa only [smul_eq_mul, Function.comp_apply] using hzero

/-- The complete explicit residue is uniformly bounded strongly enough that
its exact `1/M` contribution vanishes. -/
theorem tendsto_inv_mul_exactCutoffCameraGramResidue_zero
    {period camera₁ camera₂ : ℕ}
    (hperiod : 0 < period)
    (hcamera₁ : 2 ≤ camera₁) (hcamera₂ : 2 ≤ camera₂)
    (hcommon₁ : cameraSlope camera₁ ∣ period)
    (hcommon₂ : cameraSlope camera₂ ∣ period) :
    Tendsto (fun cutoff : ℕ ↦
      (cutoff : ℝ)⁻¹ *
        exactCutoffCameraGramResidue period cutoff camera₁ camera₂)
      atTop (nhds 0) := by
  let q : ℕ → ℝ := fun n ↦ realProfileProduct camera₁ camera₂ (n + 1)
  have hproduct : Function.Periodic
      (realProfileProduct camera₁ camera₂) period :=
    realProfileProduct_periodic hcamera₁ hcamera₂ hcommon₁ hcommon₂
  have hq : Function.Periodic q period := by
    intro n
    simpa only [q, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      hproduct (n + 1)
  have hmean : periodMean q period =
      periodicProductMean period camera₁ camera₂ := by
    have h := periodMean_natAdd hproduct 1
    rw [periodMean_realProfileProduct] at h
    simpa only [q, Nat.add_comm] using h
  let centered : ℕ → ℝ := fun n ↦
    q n - periodicProductMean period camera₁ camera₂
  have hcentered : Function.Periodic centered period := by
    intro n
    simp only [centered]
    rw [hq n]
  have hcenteredSum :
      ∑ r ∈ Finset.range period, centered r = 0 := by
    simpa only [centered, hmean] using
      (sum_period_sub_periodMean (q := q) hperiod)
  have hcoreBounded : IsBoundedUnder (· ≤ ·) atTop
      (norm ∘ fun cutoff : ℕ ↦
        ∑ n ∈ Finset.range (pairCoreLength camera₁ camera₂ cutoff),
          centered n) := by
    change ∃ bound : ℝ, ∀ᶠ cutoff : ℕ in atTop,
      ‖∑ n ∈ Finset.range (pairCoreLength camera₁ camera₂ cutoff),
          centered n‖ ≤ bound
    exact ⟨∑ r ∈ Finset.range period, ‖centered r‖,
      Filter.Eventually.of_forall fun cutoff ↦
        norm_sum_range_le_period_norm_sum hperiod hcentered hcenteredSum _⟩
  have hcoreZero : Tendsto (fun cutoff : ℕ ↦
      (cutoff : ℝ)⁻¹ *
        ∑ n ∈ Finset.range (pairCoreLength camera₁ camera₂ cutoff),
          centered n) atTop (nhds 0) := by
    have hzero :=
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).zero_smul_isBoundedUnder_le
        hcoreBounded
    simpa only [smul_eq_mul, Function.comp_apply] using hzero
  have hboundaryZero :=
    tendsto_inv_mul_finiteBoundarySum_one_zero hcamera₁ hcamera₂
  have hsum := hcoreZero.add hboundaryZero
  have hsumZero : Tendsto (fun cutoff : ℕ ↦
      (cutoff : ℝ)⁻¹ *
          ∑ n ∈ Finset.range (pairCoreLength camera₁ camera₂ cutoff),
            centered n +
        (cutoff : ℝ)⁻¹ *
          finiteBoundarySum (fun _ ↦ (1 : ℝ)) cutoff camera₁ camera₂)
      atTop (nhds 0) := by
    simpa only [add_zero] using hsum
  apply hsumZero.congr'
  filter_upwards with cutoff
  simp only [exactCutoffCameraGramResidue, centered, q]
  ring

/-- Entrywise cutoff-to-completion theorem for every finite all-bases camera
family.  It follows from the exact finite identity, not from a fitted
asymptotic model. -/
theorem tendsto_normalizedLiteralFiniteCameraGram_apply
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ}
    (hperiod : 0 < period) (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) (i j : index) :
    Tendsto (fun cutoff : ℕ ↦
      (cutoff : ℝ)⁻¹ *
        literalFiniteCameraGram cutoff (camera i) (camera j))
      atTop (nhds (periodicGramMatrix period camera i j)) := by
  have hresidue := tendsto_inv_mul_exactCutoffCameraGramResidue_zero
    hperiod (hcamera i) (hcamera j) (hcommon i) (hcommon j)
  have htotal :=
    (tendsto_const_nhds : Tendsto
      (fun _ : ℕ ↦ periodicGramMatrix period camera i j)
      atTop (nhds (periodicGramMatrix period camera i j))).add hresidue
  have htotal' : Tendsto (fun cutoff : ℕ ↦
      periodicGramMatrix period camera i j +
        (cutoff : ℝ)⁻¹ *
          exactCutoffCameraGramResidue period cutoff (camera i) (camera j))
      atTop (nhds (periodicGramMatrix period camera i j)) := by
    simpa only [add_zero] using htotal
  apply htotal'.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun _ h ↦ h⟩] with cutoff hcutoff
  exact (normalizedLiteralFiniteCameraGram_eq_periodicGram_add_residue_div
    (Nat.zero_lt_of_lt hcutoff) hcamera i j).symm

/-- Simultaneous matrix form of the literal cutoff-to-completion theorem. -/
theorem tendsto_normalizedLiteralFiniteCameraGram
    {index : Type*} [Fintype index]
    {period : ℕ} {camera : index → ℕ}
    (hperiod : 0 < period) (hcamera : ∀ i, 2 ≤ camera i)
    (hcommon : IsCommonProfilePeriod period camera) :
    Tendsto (fun cutoff : ℕ ↦
      fun i j ↦ (cutoff : ℝ)⁻¹ *
        literalFiniteCameraGram cutoff (camera i) (camera j))
      atTop (nhds (periodicGramMatrix period camera)) := by
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  exact tendsto_normalizedLiteralFiniteCameraGram_apply
    hperiod hcamera hcommon i j

/-- Concrete six-camera specialization used by the native laboratory. -/
theorem tendsto_normalizedLiteralSixCameraGram :
    Tendsto (fun cutoff : ℕ ↦
      fun i j ↦ (cutoff : ℝ)⁻¹ *
        literalFiniteCameraGram cutoff (sixCamera i) (sixCamera j))
      atTop (nhds sixCameraGram) := by
  have hcamera : ∀ i, 2 ≤ sixCamera i := by
    intro i
    fin_cases i <;> norm_num [sixCamera]
  simpa only [sixCameraGram_eq] using
    (tendsto_normalizedLiteralFiniteCameraGram
      (period := 420) (camera := sixCamera) (by norm_num)
      hcamera sixCamera_commonPeriod)

end NativeCarryC3Crosswalk

