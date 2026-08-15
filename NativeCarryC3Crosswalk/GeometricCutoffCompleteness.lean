import NativeCarrySpectralWeyl.Camera.HigherDerivativeTail
import NativeCarrySpectralWeyl.Limits.FiniteDefectCovariance

/-!
# Camera-complete native cutoffs

A native cutoff is counted by aligned bracket centers, not by a raw terminal
integer.  If `M` centers are retained, every retained center carries all of
its radii and therefore both of its legs.  The last required positive index is

* `4 * M + 1` for the exceptional aligned C2 camera;
* `b * M + floor(b / 2)` for every natural camera `b >= 3`.

This module gives that convention a small public API.  It also separates the
finite right end-cap from the analytic tail: the latter begins at center `M`
and is a sum of complete omitted center brackets.
-/

namespace NativeCarryC3Crosswalk

open FiniteNativeCarryOperator.Camera
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Camera.FiniteBridge
open NativeCarrySpectralWeyl.Limits

noncomputable section

/-- A raw positive-index horizon contains a geometrically complete native
cutoff when it contains at least one supported camera center and the full
right leg of the last retained center. -/
def IsGeometricallyCompleteNativeCutoff
    (camera cutoff rawHorizon : ℕ) : Prop :=
  2 ≤ camera ∧ 1 ≤ cutoff ∧ finiteCameraWindow camera cutoff ≤ rawHorizon

/-- The maximal number of complete centers visible through a raw horizon.
The subtraction is truncated, so a horizon shorter than the boundary width
returns zero centers. -/
def completeCenterCount (camera rawHorizon : ℕ) : ℕ :=
  (rawHorizon - cameraBoundaryWidth camera) / cameraSlope camera

/-- One raw horizon which contains `cutoff` complete centers for every camera
in the initial atlas `2, ..., largestCamera`.  C2 remains exceptional, hence
the maximum of the C2 and natural-camera formulas. -/
def initialAtlasCompleteHorizon (largestCamera cutoff : ℕ) : ℕ :=
  max (4 * cutoff + 1)
    (largestCamera * cutoff + largestCamera / 2)

/-- The boundary width is exactly the largest radius emitted by the finite
native operator, including the exceptional C2 convention. -/
theorem cameraBoundaryWidth_eq_halfRange (camera : ℕ) :
    cameraBoundaryWidth camera =
      FiniteNativeCarryOperator.Camera.halfRange camera := by
  by_cases htwo : camera = 2
  · subst camera
    rfl
  · simp [cameraBoundaryWidth_of_ne_two htwo,
      FiniteNativeCarryOperator.Camera.halfRange]

/-- The emitted window is the last center plus its largest right leg. -/
theorem finiteCameraWindow_eq_slope_add_halfRange (camera cutoff : ℕ) :
    finiteCameraWindow camera cutoff =
      cameraSlope camera * cutoff +
        FiniteNativeCarryOperator.Camera.halfRange camera := by
  simp [finiteCameraWindow, cameraBoundaryWidth_eq_halfRange]

/-- Every supported camera has positive slope. -/
theorem cameraSlope_pos_of_supported {camera : ℕ} (hcamera : 2 ≤ camera) :
    0 < cameraSlope camera := by
  by_cases htwo : camera = 2
  · subst camera
    simp
  · rw [cameraSlope_of_ne_two htwo]
    omega

/-- Every supported camera has a largest radius strictly smaller than the
distance between consecutive centers. -/
theorem halfRange_lt_cameraSlope {camera : ℕ} (hcamera : 2 ≤ camera) :
    FiniteNativeCarryOperator.Camera.halfRange camera < cameraSlope camera := by
  by_cases htwo : camera = 2
  · subst camera
    change 1 < 4
    omega
  · rw [cameraSlope_of_ne_two htwo]
    simp only [halfRange]
    omega

/-- The largest radius is one of the radii emitted by every supported camera. -/
theorem halfRange_mem_radiusSet {camera : ℕ} (hcamera : 2 ≤ camera) :
    FiniteNativeCarryOperator.Camera.halfRange camera ∈ radiusSet camera := by
  rw [mem_radiusSet_iff]
  exact ⟨halfRange_pos hcamera, le_rfl⟩

/-- Every included bracket cell is complete inside the canonical emitted
window: its left leg stays positive and its right leg stays below the exact
horizon. -/
theorem included_center_has_both_legs_in_window
    {camera cutoff index radius : ℕ}
    (hcamera : 2 ≤ camera) (hindex : index < cutoff)
    (hradius : radius ∈ radiusSet camera) :
    1 ≤ alignedCenter camera index - radius ∧
      alignedCenter camera index + radius ≤
        finiteCameraWindow camera cutoff := by
  rw [mem_radiusSet_iff] at hradius
  have hradiusLt : radius < cameraSlope camera :=
    lt_of_le_of_lt hradius.2 (halfRange_lt_cameraSlope hcamera)
  have hslopeLeCenter :
      cameraSlope camera ≤ cameraSlope camera * (index + 1) := by
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hcenterLe :
      cameraSlope camera * (index + 1) ≤ cameraSlope camera * cutoff := by
    exact Nat.mul_le_mul_left _ (by omega)
  rw [alignedCenter_eq_cameraSlope_mul,
    finiteCameraWindow_eq_slope_add_halfRange]
  constructor
  · omega
  · have hradiusHalf :
        radius ≤ FiniteNativeCarryOperator.Camera.halfRange camera :=
      hradius.2
    omega

/-- For a positive cutoff, the largest right leg of the last retained center
is literally the emitted-window endpoint. -/
theorem last_right_leg_eq_finiteCameraWindow
    {camera cutoff : ℕ} (hcutoff : 1 ≤ cutoff) :
    alignedCenter camera (cutoff - 1) +
        FiniteNativeCarryOperator.Camera.halfRange camera =
      finiteCameraWindow camera cutoff := by
  rw [alignedCenter_eq_cameraSlope_mul,
    finiteCameraWindow_eq_slope_add_halfRange]
  have hsucc : cutoff - 1 + 1 = cutoff := Nat.sub_add_cancel hcutoff
  rw [hsucc]

/-- Stopping at the last center itself always cuts off a nonempty right leg.
This is the precise defect avoided by a camera-complete cutoff. -/
theorem center_only_horizon_is_not_complete
    {camera cutoff : ℕ} (hcamera : 2 ≤ camera) :
    ¬finiteCameraWindow camera cutoff ≤ cameraSlope camera * cutoff := by
  rw [finiteCameraWindow_eq_slope_add_halfRange]
  have hhalf := halfRange_pos hcamera
  omega

/-- The exceptional C2 camera needs raw horizon `4M+1`. -/
@[simp] theorem c2_complete_horizon (cutoff : ℕ) :
    finiteCameraWindow 2 cutoff = 4 * cutoff + 1 :=
  finiteCameraWindow_two cutoff

/-- Every natural camera `b >= 3` needs raw horizon
`bM + floor(b/2)`. -/
theorem natural_complete_horizon {camera : ℕ} (hcamera : 3 ≤ camera)
    (cutoff : ℕ) :
    finiteCameraWindow camera cutoff = camera * cutoff + camera / 2 := by
  exact finiteCameraWindow_of_ne_two (by omega) cutoff

/-- Closed formula for the number of complete C2 centers through a raw
horizon. -/
@[simp] theorem completeCenterCount_two (rawHorizon : ℕ) :
    completeCenterCount 2 rawHorizon = (rawHorizon - 1) / 4 := by
  simp [completeCenterCount]

/-- Closed formula for the number of complete centers of a natural camera. -/
theorem completeCenterCount_natural {camera : ℕ} (hcamera : 3 ≤ camera)
    (rawHorizon : ℕ) :
    completeCenterCount camera rawHorizon =
      (rawHorizon - camera / 2) / camera := by
  have htwo : camera ≠ 2 := by omega
  unfold completeCenterCount
  rw [cameraBoundaryWidth_of_ne_two htwo,
    cameraSlope_of_ne_two htwo]

/-- Through a raw horizon, C2 has one complete center exactly from index `5`
onward. -/
theorem c2_one_complete_center_iff {rawHorizon : ℕ} :
    IsGeometricallyCompleteNativeCutoff 2 1 rawHorizon ↔
      5 ≤ rawHorizon := by
  simp [IsGeometricallyCompleteNativeCutoff]

/-- A natural camera first becomes geometrically active only when the raw
horizon contains its center and its entire maximal right leg. -/
theorem natural_one_complete_center_iff
    {camera rawHorizon : ℕ} (hcamera : 3 ≤ camera) :
    IsGeometricallyCompleteNativeCutoff camera 1 rawHorizon ↔
      camera + camera / 2 ≤ rawHorizon := by
  have hsupported : 2 ≤ camera := by omega
  simp [IsGeometricallyCompleteNativeCutoff,
    natural_complete_horizon hcamera, hsupported]

/-- The coupled atlas horizon really contains every complete camera cell in
the initial atlas.  High bases receive a larger physical window even though
all cameras use the same number of centers. -/
theorem finiteCameraWindow_le_initialAtlasCompleteHorizon
    {camera largestCamera cutoff : ℕ} (hcamera : 2 ≤ camera)
    (hle : camera ≤ largestCamera) :
    finiteCameraWindow camera cutoff ≤
      initialAtlasCompleteHorizon largestCamera cutoff := by
  by_cases htwo : camera = 2
  · subst camera
    rw [finiteCameraWindow_two]
    exact Nat.le_max_left _ _
  · have hthree : 3 ≤ camera := by omega
    rw [natural_complete_horizon hthree]
    apply le_trans _ (Nat.le_max_right _ _)
    exact Nat.add_le_add (Nat.mul_le_mul_right cutoff hle)
      (Nat.div_le_div_right hle)

/-- Positive common center cutoffs are geometrically complete for every
supported camera in the initial atlas. -/
theorem initialAtlasCompleteHorizon_is_complete
    {camera largestCamera cutoff : ℕ} (hcamera : 2 ≤ camera)
    (hle : camera ≤ largestCamera) (hcutoff : 1 ≤ cutoff) :
    IsGeometricallyCompleteNativeCutoff camera cutoff
      (initialAtlasCompleteHorizon largestCamera cutoff) :=
  ⟨hcamera, hcutoff,
    finiteCameraWindow_le_initialAtlasCompleteHorizon hcamera hle⟩

/-- If the boundary width already fits in the raw horizon, the quotient in
`completeCenterCount` is the exact maximality criterion for complete cells. -/
theorem cutoff_le_completeCenterCount_iff
    {camera cutoff rawHorizon : ℕ} (hcamera : 2 ≤ camera)
    (hboundary : cameraBoundaryWidth camera ≤ rawHorizon) :
    cutoff ≤ completeCenterCount camera rawHorizon ↔
      finiteCameraWindow camera cutoff ≤ rawHorizon := by
  constructor
  · intro hcount
    have hmul :
        cutoff * cameraSlope camera ≤
          rawHorizon - cameraBoundaryWidth camera :=
      (Nat.le_div_iff_mul_le
        (cameraSlope_pos_of_supported hcamera)).mp hcount
    have hmul' :
        cameraSlope camera * cutoff ≤
          rawHorizon - cameraBoundaryWidth camera := by
      simpa [Nat.mul_comm] using hmul
    exact Nat.add_le_of_le_sub hboundary hmul'
  · intro hwindow
    have hsub :
        cameraSlope camera * cutoff ≤
          rawHorizon - cameraBoundaryWidth camera := by
      exact Nat.le_sub_of_add_le hwindow
    apply (Nat.le_div_iff_mul_le
      (cameraSlope_pos_of_supported hcamera)).mpr
    simpa [Nat.mul_comm] using hsub

/-- The canonical quotient really gives a complete cutoff whenever at least
one center fits. -/
theorem completeCenterCount_is_complete
    {camera rawHorizon : ℕ} (hcamera : 2 ≤ camera)
    (hone : 1 ≤ completeCenterCount camera rawHorizon) :
    IsGeometricallyCompleteNativeCutoff camera
      (completeCenterCount camera rawHorizon) rawHorizon := by
  refine ⟨hcamera, hone, ?_⟩
  apply (cutoff_le_completeCenterCount_iff hcamera ?_).mp
  · exact le_rfl
  · by_contra hnot
    have hlt : rawHorizon < cameraBoundaryWidth camera := by omega
    have hzero : completeCenterCount camera rawHorizon = 0 := by
      simp [completeCenterCount, Nat.sub_eq_zero_of_le hlt.le]
    omega

/-- A common finite-family window is camera-complete for every supported
member as soon as the common center cutoff is positive. -/
theorem finiteFamilyWindow_is_camera_complete
    {index : Type*} [Fintype index] (camera : index → ℕ)
    (hcamera : ∀ i, 2 ≤ camera i) {cutoff : ℕ} (hcutoff : 1 ≤ cutoff)
    (i : index) :
    IsGeometricallyCompleteNativeCutoff (camera i) cutoff
      (finiteFamilyWindow cutoff camera) := by
  exact ⟨hcamera i, hcutoff,
    finiteCameraWindow_le_finiteFamilyWindow cutoff camera i⟩

/-- No coefficient survives beyond the camera-complete horizon. -/
theorem finiteCoefficient_eq_zero_above_complete_horizon
    {camera cutoff position : ℕ} (hcamera : 2 ≤ camera)
    (hout : finiteCameraWindow camera cutoff < position) :
    finiteCoefficient camera cutoff position = 0 :=
  finiteCoefficient_eq_zero_of_window_lt hcamera hout

/-- On an even camera, the final antipodal point is already the right leg of
the last retained cell (coefficient `1`).  Its second incidence belongs to
the first omitted cell, so the infinite periodic profile has coefficient
`2` there. -/
theorem even_endpoint_records_head_tail_incidence
    {camera cutoff : ℕ} (hcamera : 4 ≤ camera) (heven : Even camera) :
    finiteCoefficient camera cutoff (finiteCameraWindow camera cutoff) = 1 ∧
      evenProfile camera (finiteCameraWindow camera cutoff) = 2 := by
  rw [finiteCameraWindow_of_ne_two (by omega : camera ≠ 2)]
  exact ⟨even_finiteCoefficient_endpoint hcamera heven,
    evenProfile_endpoint hcamera heven⟩

/-- Exact head--tail ledger: the analytic remainder begins at the next whole
center bracket.  It never starts at a dangling leg. -/
theorem complete_head_add_complete_center_tail
    {camera cutoff : ℕ} (hcamera : 2 ≤ camera) (time : ℝ) :
    finiteBracketCharacteristic camera cutoff (nativeLine time) +
        (∑' index : ℕ,
          centerBracketTerm camera (nativeLine time) (index + cutoff)) =
      bracketCharacteristic camera (nativeLine time) := by
  have htail :=
    bracketCharacteristic_sub_finite_eq_tsum_nat_add
      (camera := camera) (cutoff := cutoff) hcamera time
  rw [← htail]
  ring

/-- Off the native line as well, throughout the bracket domain, the analytic
tail is a sum of whole omitted center cells. -/
theorem complete_head_add_complete_center_tail_of_mem_domain
    {camera cutoff : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ bracketDomain) :
    finiteBracketCharacteristic camera cutoff s +
        (∑' index : ℕ, centerBracketTerm camera s (index + cutoff)) =
      bracketCharacteristic camera s := by
  have htail :=
    bracketCharacteristic_sub_finite_eq_tsum_nat_add_of_mem_domain
      (camera := camera) (cutoff := cutoff) hcamera hs
  rw [← htail]
  ring

/-- Camera-complete head, whole-cell tail, and the common native scalar are
one exact ledger.  This identity is established for arbitrary parameters in
the scalar domain and assumes no zero, no critical line, and no isotropy. -/
theorem complete_head_add_complete_center_tail_eq_factor_mul_nativeScalar
    {camera cutoff : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ nativeScalarDomain) :
    finiteBracketCharacteristic camera cutoff s +
        (∑' index : ℕ, centerBracketTerm camera s (index + cutoff)) =
      factor camera s * nativeScalar s := by
  have hbracket : s ∈ bracketDomain := by
    simpa [nativeScalarDomain, bracketDomain] using hs.1
  rw [complete_head_add_complete_center_tail_of_mem_domain hcamera hbracket,
    bracketCharacteristic_eq_factor_mul_nativeScalar hcamera hs]

/-- At a zero of the common scalar, every camera-complete finite head is the
negative of its whole-center analytic tail.  The theorem retains, rather than
silently discarding, the possibility of head--tail compensation. -/
theorem finite_head_eq_neg_complete_center_tail_of_nativeScalar_zero
    {camera cutoff : ℕ} (hcamera : 2 ≤ camera) {s : ℂ}
    (hs : s ∈ nativeScalarDomain) (hzero : nativeScalar s = 0) :
    finiteBracketCharacteristic camera cutoff s =
      -(∑' index : ℕ, centerBracketTerm camera s (index + cutoff)) := by
  have hledger :=
    complete_head_add_complete_center_tail_eq_factor_mul_nativeScalar
      (camera := camera) (cutoff := cutoff) hcamera hs
  rw [hzero, mul_zero] at hledger
  exact eq_neg_of_add_eq_zero_left hledger

end

end NativeCarryC3Crosswalk
