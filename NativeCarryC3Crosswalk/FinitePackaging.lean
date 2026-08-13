import CPFormal.Analytic.CpGenuineNativeRealBoundaryCrosswalk
import NativeCarrySpectralWeyl.Camera.BracketProfileBridge

/-!
# Exact C3 real--complex finite crosswalk

This module compares the pinned finite real operator with the pinned finite
Dirichlet characteristic through their common formal stencil.  Complex
notation is used only as the additive packaging of the two real coordinates.
-/

namespace NativeCarryC3Crosswalk

open FiniteNativeCarryOperator
open NativeCarrySpectralWeyl.Camera
open NativeCarrySpectralWeyl.Camera.FiniteBridge

noncomputable section

/-- The two upstream native samples are the same real pair. -/
theorem nativeState_eq_nativeCarryRealPlaneSample
    (time : ℝ) (n : ℕ) :
    Operator.nativeState time n =
      CPFormal.Analytic.Cp.nativeCarryRealPlaneSample time (n : ℤ) := by
  cases n with
  | zero =>
      simp [Operator.nativeState, Operator.nativeAmplitude,
        CPFormal.Analytic.Cp.nativeCarryRealPlaneSample,
        CPFormal.Analytic.Cp.nativeCarryRealPlaneSampleAt]
  | succ n =>
      have hn : (0 : ℤ) < ((n + 1 : ℕ) : ℤ) := by omega
      have hexponent : (-(1 : ℝ) / 2) = -((2 : ℝ)⁻¹) := by norm_num
      rw [CPFormal.Analytic.Cp.nativeCarryRealPlaneSample,
        CPFormal.Analytic.Cp.nativeCarryRealPlaneSampleAt_of_pos
          ((1 : ℝ) / 2) time hn]
      simp [Operator.nativeState, Operator.nativeAmplitude, hexponent]

/-- The two upstream notations for the critical complex parameter coincide. -/
@[simp] theorem nativeCarryRealPlaneParameter_half_eq_nativeLine
    (time : ℝ) :
    CPFormal.Analytic.Cp.nativeCarryRealPlaneParameter
        ((2 : ℝ)⁻¹) time = nativeLine time := by
  apply Complex.ext <;>
    simp [CPFormal.Analytic.Cp.nativeCarryRealPlaneParameter, nativeLine]

/-- Packaging the upstream real sample gives the upstream Dirichlet sample. -/
theorem packaged_nativeState_eq_dirichletValue_nativeLine
    (time : ℝ) (n : ℕ) :
    CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
        (Operator.nativeState time n) =
      dirichletValue (nativeLine time) n := by
  rw [nativeState_eq_nativeCarryRealPlaneSample]
  cases n with
  | zero =>
      simp only [CPFormal.Analytic.Cp.nativeCarryRealPlaneSample,
        CPFormal.Analytic.Cp.nativeCarryRealPlaneSampleAt,
        lt_self_iff_false, ↓reduceIte,
        map_zero, dirichletValue, Nat.cast_zero]
      have hnonzero : -nativeLine time ≠ 0 := by
        intro hzero
        have hre := congrArg Complex.re hzero
        simp [nativeLine] at hre
      exact (Complex.zero_cpow hnonzero).symm
  | succ n =>
      have hn : (0 : ℤ) < ((n + 1 : ℕ) : ℤ) := by omega
      have hsample :=
        CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging_sampleAt_eq_dirichletTerm
          ((1 : ℝ) / 2) time hn
      rw [CPFormal.Analytic.Cp.nativeCarryRealPlaneSample]
      rw [hsample]
      simp [CPFormal.Analytic.Cp.dirichletTerm,
        dirichletValue]

/-- Packaging commutes with evaluation of every formal integer stencil. -/
theorem packagedEvalStencil_eq_evalDirichletStencil (time : ℝ) :
    CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging.toIntLinearMap.comp
        (evalStencil time) =
      evalDirichletStencil (nativeLine time) := by
  apply Finsupp.lhom_ext
  intro n coefficient
  have hsingle : (Finsupp.single n coefficient : FormalStencil) =
      coefficient • atom n := by
    simp [atom]
  rw [hsingle]
  simp [packaged_nativeState_eq_dirichletValue_nativeLine]

/--
The pinned finite real operator and the pinned finite bracket characteristic
are the same finite computation in real-pair and complex coordinates.  The
statement holds for every natural camera, including the exceptional C2 and
the even-camera endpoint convention, because both sides evaluate the same
formal stencil.
-/
theorem packaged_finiteNativeOperator_eq_finiteBracketCharacteristic
    (time : ℝ) (camera cutoff : ℕ) :
    CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging
        (Operator.finiteNativeOperator camera cutoff time) =
      finiteBracketCharacteristic camera cutoff (nativeLine time) := by
  have h := LinearMap.congr_fun
    (packagedEvalStencil_eq_evalDirichletStencil time)
    (finiteStencil camera cutoff)
  simpa [evalStencil_finiteStencil,
    evalDirichletStencil_finiteStencil] using h

/-- Complex packaging neither creates nor removes a finite operator zero. -/
theorem finiteNativeOperator_eq_zero_iff_finiteBracketCharacteristic_eq_zero
    (time : ℝ) (camera cutoff : ℕ) :
    Operator.finiteNativeOperator camera cutoff time = 0 ↔
      finiteBracketCharacteristic camera cutoff (nativeLine time) = 0 := by
  constructor
  · intro hreal
    have hpack :=
      packaged_finiteNativeOperator_eq_finiteBracketCharacteristic
        time camera cutoff
    rw [hreal, map_zero] at hpack
    exact hpack.symm
  · intro hcomplex
    apply CPFormal.Analytic.Cp.nativeCarryRealPlaneComplexPackaging_injective
    rw [map_zero]
    rw [packaged_finiteNativeOperator_eq_finiteBracketCharacteristic,
      hcomplex]

/-- The complex squared norm is exactly the real quadratic resultant energy. -/
theorem normSq_finiteBracketCharacteristic_eq_realEnergy
    (time : ℝ) (camera cutoff : ℕ) :
    Complex.normSq
        (finiteBracketCharacteristic camera cutoff (nativeLine time)) =
      CPFormal.Analytic.Cp.nativeCarryRealPlaneEnergy
        (Operator.finiteNativeOperator camera cutoff time) := by
  rw [← packaged_finiteNativeOperator_eq_finiteBracketCharacteristic]
  exact
    CPFormal.Analytic.Cp.normSq_nativeCarryRealPlaneComplexPackaging _

end

end NativeCarryC3Crosswalk
