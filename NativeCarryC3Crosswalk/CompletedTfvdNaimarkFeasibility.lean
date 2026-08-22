import NativeCarryC3Crosswalk.EnrichedBoundaryCarrier
import NativeCarryC3Crosswalk.CanonicalNaimarkStateReadout
import CPFormal.Analytic.CpTfvdSameEdgeCompletedPrecompressionCollapse
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

/-!
# Completed TFVD ledger and faithful C3--Naimark realization

The exact same-edge collapse retains a residual energy, but its
canonical image is supported on one fixed tower coordinate.  This file makes
that rank-one fact explicit: every real-linear realization of the collapsed
residual alone has collinear canonical values.

The lossless source therefore keeps the ordinary state, the logarithmic jet,
and the residual as separate ledger entries.  Independently, one complete C3
block (three arithmetic cells on each Green leg) is packed into six literal
all-bases cameras.  Real and imaginary
parts occupy the two realified channels, so all twelve real coordinates are
retained.  The packing is a bounded injective real-linear map, and composition
with the canonical Naimark port gives a bounded injective ambient realization.
The canonical adjoint readout recovers the packed C3 state exactly.

This is a feasibility and obstruction theorem.  It constructs no inverse from
the rank-one residual to the six-coordinate C3 port and does not identify the TFVD
residual scalar with the C3 Green form.  Such an identification remains a
separate intertwining datum.
-/

open scoped ENNReal RealInnerProductSpace

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Infinite

noncomputable section

/-! ## Lossless completed TFVD ledger and rank-one audit -/

/-- The uncollapsed completed TFVD datum: ordinary state, logarithmic jet,
and the two-channel precompression residual. -/
abbrev CompletedTfvdGreenLedger :=
  (NativeGpreTfvdProductState × NativeGpreTfvdProductState) ×
    NativeGpreTfvdCompletedPrecompressionSource

/-- Canonical cutoff ledger before any attempt to reconstruct a C3 port from
the scalar residual. -/
def seededCompletedTfvdGreenLedger (M : ℕ) (s : ℂ) :
    CompletedTfvdGreenLedger :=
  let ordinary :=
    nativeGpreTfvdSameEdgeGlue nativeGpreCanonicalVerticalRealization
      (c2DirichletGradientPrefixCore s (3 * M))
  let logJet :=
    nativeGpreTfvdSameEdgeGlue nativeGpreCanonicalVerticalRealization
      (c2LogJetPrefixCore s (3 * M))
  ((ordinary, logJet),
    nativeGpreTfvdSameEdgeCompletedPrecompressionCollapseAt (3 * M)
      ordinary logJet)

@[simp] theorem seededCompletedTfvdGreenLedger_ordinary
    (M : ℕ) (s : ℂ) :
    (seededCompletedTfvdGreenLedger M s).1.1 =
      nativeGpreTfvdSameEdgeGlue nativeGpreCanonicalVerticalRealization
        (c2DirichletGradientPrefixCore s (3 * M)) := by
  rfl

@[simp] theorem seededCompletedTfvdGreenLedger_logJet
    (M : ℕ) (s : ℂ) :
    (seededCompletedTfvdGreenLedger M s).1.2 =
      nativeGpreTfvdSameEdgeGlue nativeGpreCanonicalVerticalRealization
        (c2LogJetPrefixCore s (3 * M)) := by
  rfl

@[simp] theorem seededCompletedTfvdGreenLedger_residual
    (M : ℕ) (s : ℂ) :
    (seededCompletedTfvdGreenLedger M s).2 =
      seededTfvdGpreCompletedPrecompressionSource
        (nativeGpreTfvdSameEdgeCompletedPrecompressionCollapseAt (3 * M))
        M s := by
  rfl

/-- Fixed generator of the canonical completed residual ray. -/
def completedTfvdResidualGenerator :
    NativeGpreTfvdCompletedPrecompressionSource :=
  (0, lp.single 2 1 1)

/-- The canonical collapsed residual has exactly one real degree of freedom:
the reflected energy coefficient multiplying a fixed tower generator. -/
theorem seededCompletedTfvdGreenLedger_residual_eq_smul
    (M : ℕ) (s : ℂ) :
    (seededCompletedTfvdGreenLedger M s).2 =
      (finiteReflectedGradientPairing (3 * M) s).re •
        completedTfvdResidualGenerator := by
  rw [seededCompletedTfvdGreenLedger_residual,
    seededTfvdGpreCompletedPrecompressionSource_sameEdge]
  apply Prod.ext
  · simp [completedTfvdResidualGenerator]
  · apply lp.ext
    funext n
    by_cases h : n = 1 <;>
      simp [completedTfvdResidualGenerator,
        nativeGpreGreenEnergyFirstLevelState, lp.single_apply, h]

/-- Every real-linear image of the canonical residual remains on the image of
one fixed generator.  Thus a residual-only linear realization is rank at most
one on the canonical family. -/
theorem map_seededCompletedTfvdGreenLedger_residual_eq_smul
    {H : Type*} [AddCommGroup H] [Module ℝ H]
    (T : NativeGpreTfvdCompletedPrecompressionSource →ₗ[ℝ] H)
    (M : ℕ) (s : ℂ) :
    T (seededCompletedTfvdGreenLedger M s).2 =
      (finiteReflectedGradientPairing (3 * M) s).re •
        T completedTfvdResidualGenerator := by
  rw [seededCompletedTfvdGreenLedger_residual_eq_smul, map_smul]

/-! ## Faithful six-camera packing of one complete C3 block -/

/-- Camera labels `2,3,4` assigned to the first C3 Green leg. -/
def firstC3CameraIndex (i : Fin 3) : CameraIndex :=
  ⟨i.val + 2, by omega⟩

/-- Camera labels `5,6,7` assigned to the second C3 Green leg. -/
def secondC3CameraIndex (i : Fin 3) : CameraIndex :=
  ⟨i.val + 5, by omega⟩

/-- Real parts of the six complex C3 coordinates. -/
def c3RealCameraFinsupp (x : FiniteC3GreenPortCarrier 3) :
    CameraFinsupp :=
  (∑ i : Fin 3,
      Finsupp.single (firstC3CameraIndex i) (x.1 i).re) +
    ∑ i : Fin 3,
      Finsupp.single (secondC3CameraIndex i) (x.2 i).re

/-- Imaginary parts of the six complex C3 coordinates. -/
def c3ImagCameraFinsupp (x : FiniteC3GreenPortCarrier 3) :
    CameraFinsupp :=
  (∑ i : Fin 3,
      Finsupp.single (firstC3CameraIndex i) (x.1 i).im) +
    ∑ i : Fin 3,
      Finsupp.single (secondC3CameraIndex i) (x.2 i).im

@[simp] theorem c3RealCameraFinsupp_first
    (x : FiniteC3GreenPortCarrier 3) (j : Fin 3) :
    c3RealCameraFinsupp x (firstC3CameraIndex j) = (x.1 j).re := by
  fin_cases j <;>
    simp [c3RealCameraFinsupp, firstC3CameraIndex,
      secondC3CameraIndex, Fin.sum_univ_succ]

@[simp] theorem c3RealCameraFinsupp_second
    (x : FiniteC3GreenPortCarrier 3) (j : Fin 3) :
    c3RealCameraFinsupp x (secondC3CameraIndex j) = (x.2 j).re := by
  fin_cases j <;>
    simp [c3RealCameraFinsupp, firstC3CameraIndex,
      secondC3CameraIndex, Fin.sum_univ_succ]

@[simp] theorem c3ImagCameraFinsupp_first
    (x : FiniteC3GreenPortCarrier 3) (j : Fin 3) :
    c3ImagCameraFinsupp x (firstC3CameraIndex j) = (x.1 j).im := by
  fin_cases j <;>
    simp [c3ImagCameraFinsupp, firstC3CameraIndex,
      secondC3CameraIndex, Fin.sum_univ_succ]

@[simp] theorem c3ImagCameraFinsupp_second
    (x : FiniteC3GreenPortCarrier 3) (j : Fin 3) :
    c3ImagCameraFinsupp x (secondC3CameraIndex j) = (x.2 j).im := by
  fin_cases j <;>
    simp [c3ImagCameraFinsupp, firstC3CameraIndex,
      secondC3CameraIndex, Fin.sum_univ_succ]

/-- The coefficient-level real/imaginary packing is real-linear. -/
def c3CameraFinsuppPairLinearMap :
    FiniteC3GreenPortCarrier 3 →ₗ[ℝ] (CameraFinsupp × CameraFinsupp) where
  toFun x := (c3RealCameraFinsupp x, c3ImagCameraFinsupp x)
  map_add' x y := by
    apply Prod.ext <;> ext camera
    · simp [c3RealCameraFinsupp, Finsupp.single_add,
        Finset.sum_add_distrib]
      abel
    · simp [c3ImagCameraFinsupp, Finsupp.single_add,
        Finset.sum_add_distrib]
      abel
  map_smul' r x := by
    apply Prod.ext <;> ext camera
    · simp [c3RealCameraFinsupp, Complex.real_smul,
        Finsupp.smul_single, Finset.smul_sum]
    · simp [c3ImagCameraFinsupp, Complex.real_smul,
        Complex.ofReal_mul', Finsupp.smul_single, Finset.smul_sum]

/-- All twelve real coordinates are retained at coefficient level. -/
theorem c3CameraFinsuppPairLinearMap_injective :
    Function.Injective c3CameraFinsuppPairLinearMap := by
  intro x y hxy
  have hreal : c3RealCameraFinsupp x = c3RealCameraFinsupp y :=
    congrArg Prod.fst hxy
  have himag : c3ImagCameraFinsupp x = c3ImagCameraFinsupp y :=
    congrArg Prod.snd hxy
  apply Prod.ext
  · apply WithLp.ofLp_injective 2
    funext i
    apply Complex.ext
    · have h := congrArg
        (fun u : CameraFinsupp => u (firstC3CameraIndex i)) hreal
      simpa using h
    · have h := congrArg
        (fun u : CameraFinsupp => u (firstC3CameraIndex i)) himag
      simpa using h
  · apply WithLp.ofLp_injective 2
    funext i
    apply Complex.ext
    · have h := congrArg
        (fun u : CameraFinsupp => u (secondC3CameraIndex i)) hreal
      simpa using h
    · have h := congrArg
        (fun u : CameraFinsupp => u (secondC3CameraIndex i)) himag
      simpa using h

/-- One complete C3 block packed into the realified all-bases camera
completion. -/
def c3SixCameraPackingLinearMap :
    FiniteC3GreenPortCarrier 3 →ₗ[ℝ] RealifiedCameraComplexification where
  toFun x := WithLp.toLp 2
    (cameraEmbedding (c3RealCameraFinsupp x),
      cameraEmbedding (c3ImagCameraFinsupp x))
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    have h := c3CameraFinsuppPairLinearMap.map_add x y
    apply Prod.ext
    · change cameraEmbedding (c3RealCameraFinsupp (x + y)) =
        cameraEmbedding (c3RealCameraFinsupp x) +
          cameraEmbedding (c3RealCameraFinsupp y)
      rw [show c3RealCameraFinsupp (x + y) =
        c3RealCameraFinsupp x + c3RealCameraFinsupp y from
          congrArg Prod.fst h, map_add]
    · change cameraEmbedding (c3ImagCameraFinsupp (x + y)) =
        cameraEmbedding (c3ImagCameraFinsupp x) +
          cameraEmbedding (c3ImagCameraFinsupp y)
      rw [show c3ImagCameraFinsupp (x + y) =
        c3ImagCameraFinsupp x + c3ImagCameraFinsupp y from
          congrArg Prod.snd h, map_add]
  map_smul' r x := by
    apply WithLp.ofLp_injective 2
    have h := c3CameraFinsuppPairLinearMap.map_smul r x
    apply Prod.ext
    · change cameraEmbedding (c3RealCameraFinsupp (r • x)) =
        r • cameraEmbedding (c3RealCameraFinsupp x)
      rw [show c3RealCameraFinsupp (r • x) =
        r • c3RealCameraFinsupp x from congrArg Prod.fst h, map_smul]
    · change cameraEmbedding (c3ImagCameraFinsupp (r • x)) =
        r • cameraEmbedding (c3ImagCameraFinsupp x)
      rw [show c3ImagCameraFinsupp (r • x) =
        r • c3ImagCameraFinsupp x from congrArg Prod.snd h, map_smul]

/-- The finite-dimensional source makes the faithful packing automatically
bounded. -/
def c3SixCameraPacking :
    FiniteC3GreenPortCarrier 3 →L[ℝ] RealifiedCameraComplexification :=
  LinearMap.toContinuousLinearMap c3SixCameraPackingLinearMap

@[simp] theorem c3SixCameraPacking_apply
    (x : FiniteC3GreenPortCarrier 3) :
    c3SixCameraPacking x = WithLp.toLp 2
      (cameraEmbedding (c3RealCameraFinsupp x),
        cameraEmbedding (c3ImagCameraFinsupp x)) :=
  rfl

/-- Completion and realification do not collapse a C3 port. -/
theorem c3SixCameraPacking_injective :
    Function.Injective c3SixCameraPacking := by
  intro x y hxy
  have hpair := congrArg
    (WithLp.ofLp : RealifiedCameraComplexification →
      CameraHilbert × CameraHilbert) hxy
  apply c3CameraFinsuppPairLinearMap_injective
  apply Prod.ext
  · exact cameraEmbedding.injective (congrArg Prod.fst hpair)
  · exact cameraEmbedding.injective (congrArg Prod.snd hpair)

/-! ## Canonical Naimark promotion -/

/-- Ambient Naimark realization of the complete C3 port. -/
def c3SixCameraNaimarkRealization :
    FiniteC3GreenPortCarrier 3 →L[ℝ]
      RealifiedNaimarkComplexification :=
  realifiedNaimarkPort ∘L c3SixCameraPacking

/-- The Naimark realization remains faithful. -/
theorem c3SixCameraNaimarkRealization_injective :
    Function.Injective c3SixCameraNaimarkRealization := by
  intro x y hxy
  apply c3SixCameraPacking_injective
  apply realifiedNaimarkPort_injective
  exact hxy

/-- Canonical Naimark compression recovers the complete packed C3 port, with
no section or pseudoinverse. -/
theorem canonicalCameraStateReadout_c3SixCameraNaimarkRealization :
    canonicalCameraStateReadout c3SixCameraNaimarkRealization =
      c3SixCameraPacking := by
  exact canonicalCameraStateReadout_of_coherent c3SixCameraPacking

/-- The realified Green skew form used to compare intrinsic and ambient
realizations. -/
def realifiedGreenSkew
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x y : WithLp 2 (H × H)) : ℝ :=
  inner ℝ x.fst y.snd - inner ℝ x.snd y.fst

/-- The coordinatewise Naimark isometry preserves the Green skew form
exactly. -/
theorem realifiedGreenSkew_realifiedNaimarkPort
    (x y : RealifiedCameraComplexification) :
    realifiedGreenSkew (realifiedNaimarkPort x)
        (realifiedNaimarkPort y) =
      realifiedGreenSkew x y := by
  simp only [realifiedGreenSkew, realifiedNaimarkPort_fst,
    realifiedNaimarkPort_snd]
  show
    inner ℝ (naimarkIsometry x.fst) (naimarkIsometry y.snd) -
        inner ℝ (naimarkIsometry x.snd) (naimarkIsometry y.fst) =
      inner ℝ x.fst y.snd - inner ℝ x.snd y.fst
  rw [naimarkIsometry.inner_map_map, naimarkIsometry.inner_map_map]

/-- Hence the concrete C3--Naimark realization preserves the Green skew form
pulled back from its faithful camera packing. -/
theorem realifiedGreenSkew_c3SixCameraNaimarkRealization
    (x y : FiniteC3GreenPortCarrier 3) :
    realifiedGreenSkew (c3SixCameraNaimarkRealization x)
        (c3SixCameraNaimarkRealization y) =
      realifiedGreenSkew (c3SixCameraPacking x)
        (c3SixCameraPacking y) := by
  exact realifiedGreenSkew_realifiedNaimarkPort
    (c3SixCameraPacking x) (c3SixCameraPacking y)

end

end NativeCarryC3Crosswalk
