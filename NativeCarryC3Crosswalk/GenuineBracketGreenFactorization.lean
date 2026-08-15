import NativeCarryC3Crosswalk.GenuineBracketGreenIdentity
import CPFormal.Analytic.CpNativeCarryAngularCorrectionExactLimit

/-!
# Exact Genuine-bracket Green factorization and its frontier

The differentiated Genuine bracket already produces the complete finite C3
Green port.  This module resolves the resulting boundary form one step
further.  At every cutoff it factors exactly as

`radial tilt * reflected Green pairing`.

The factorization is unconditional.  In the open Genuine strip the reflected
pairing has a nonzero limit, so convergence of this concrete Green form to
zero is equivalent to `Re(s) = 1 / 2`.

The scalar Genuine cancellation is recorded separately.  At a Genuine zero it
annihilates the sum of the Green form and the independently defined angular
provenance correction.  The correction has exactly the opposite limiting
value of the Green form; it is not a tail that may be discarded.  Consequently
the remaining zero-to-Green closure statement is displayed as precisely the
strong nonvanishing frontier, rather than hidden inside a factorization.
-/

open scoped Topology

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary
open Filter

noncomputable section

/-- Exact finite radial factorization of the boundary form constructed from
the differentiated Genuine bracket.  No zero, strip, or limit hypothesis is
used. -/
theorem greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_radialFactorization
    (M : ℕ) (s : ℂ) :
    greenForm (𝕜 := ℂ)
        (finiteC3GenuineBracketGreenBoundaryPair M s)
        (finiteC3GenuineBracketGreenBoundaryPair M (reflectedParameter s)) =
      ((cpRadialDifference 3 (criticalDisplacement s.re) : ℝ) : ℂ) *
        finiteReflectedGradientPairing M s := by
  rw [greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_genuineFlux,
    finiteOrientedGenuineCpGreenFlux_eq_finiteOrientedCpGreenFlux
      3 M (by norm_num),
    finiteOrientedCpGreenFlux_eq_radialDifference_mul_pairing
      3 M (by norm_num)]

/-- The finite Genuine-bracket Green forms converge to their explicit radial
factor times the infinite reflected pairing. -/
theorem greenForm_finiteC3GenuineBracketGreenBoundaryPair_tendsto
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Tendsto
      (fun M : ℕ ↦
        greenForm (𝕜 := ℂ)
          (finiteC3GenuineBracketGreenBoundaryPair M s)
          (finiteC3GenuineBracketGreenBoundaryPair M
            (reflectedParameter s)))
      atTop
      (nhds
        (((cpRadialDifference 3
            (criticalDisplacement s.re) : ℝ) : ℂ) *
          infiniteReflectedGradientPairing s)) := by
  have hpairing := finiteReflectedGradientPairing_tendsto_infinite hs
  have hscaled :=
    (tendsto_const_nhds :
      Tendsto
        (fun _ : ℕ ↦
          ((cpRadialDifference 3
            (criticalDisplacement s.re) : ℝ) : ℂ))
        atTop
        (nhds
          ((cpRadialDifference 3
            (criticalDisplacement s.re) : ℝ) : ℂ))).mul hpairing
  simpa only
      [greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_radialFactorization]
    using hscaled

/-- In the open Genuine strip, closure of this concrete bracket-resolved Green
form is exactly the quadratic equilibrium.  This theorem has no Genuine-zero
hypothesis. -/
theorem greenForm_finiteC3GenuineBracketGreenBoundaryPair_tendsto_zero_iff
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Tendsto
        (fun M : ℕ ↦
          greenForm (𝕜 := ℂ)
            (finiteC3GenuineBracketGreenBoundaryPair M s)
            (finiteC3GenuineBracketGreenBoundaryPair M
              (reflectedParameter s)))
        atTop (nhds 0) ↔
      s.re = (1 : ℝ) / 2 := by
  constructor
  · intro hcloses
    have hlimit :=
      greenForm_finiteC3GenuineBracketGreenBoundaryPair_tendsto hs
    have hproduct :
        (((cpRadialDifference 3
            (criticalDisplacement s.re) : ℝ) : ℂ) *
          infiniteReflectedGradientPairing s) = 0 :=
      tendsto_nhds_unique hlimit hcloses
    have henergy : infiniteReflectedGradientPairing s ≠ 0 :=
      infiniteReflectedGradientPairing_ne_zero hs
    have hcoefficient :
        ((cpRadialDifference 3
          (criticalDisplacement s.re) : ℝ) : ℂ) = 0 :=
      (mul_eq_zero.mp hproduct).resolve_right henergy
    have hradial :
        cpRadialDifference 3 (criticalDisplacement s.re) = 0 := by
      exact_mod_cast hcoefficient
    have hcritical : criticalDisplacement s.re = 0 :=
      (cpRadialDifference_eq_zero_iff
        3 (by norm_num) (criticalDisplacement s.re)).1 hradial
    unfold criticalDisplacement at hcritical
    linarith
  · intro hre
    have hcritical : criticalDisplacement s.re = 0 := by
      unfold criticalDisplacement
      linarith
    have hpoint :
        (fun M : ℕ ↦
          greenForm (𝕜 := ℂ)
            (finiteC3GenuineBracketGreenBoundaryPair M s)
            (finiteC3GenuineBracketGreenBoundaryPair M
              (reflectedParameter s))) =
          fun _ : ℕ ↦ 0 := by
      funext M
      rw [
        greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_radialFactorization,
        hcritical]
      simp [cpRadialDifference]
    rw [hpoint]
    exact tendsto_const_nhds

/-- At a Genuine zero, scalar angular cancellation closes the Green form only
together with the independently defined provenance correction. -/
theorem genuineZero_greenForm_add_scaledAngularCorrection_tendsto_zero
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    Tendsto
      (fun M : ℕ ↦
        greenForm (𝕜 := ℂ)
            (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
            (finiteC3GenuineBracketGreenBoundaryPair
              (3 * M) (reflectedParameter s)) +
          ((cpRadialDifference 3
            (criticalDisplacement s.re) : ℝ) : ℂ) *
            finiteCanonicalAngularGreenCorrection M s)
      atTop (nhds 0) := by
  have hbudget :=
    finiteCanonicalAngularGreenBudget_tendsto_zero_of_genuine_zero hs hzero
  have hscaled :=
    (tendsto_const_nhds :
      Tendsto
        (fun _ : ℕ ↦
          ((cpRadialDifference 3
            (criticalDisplacement s.re) : ℝ) : ℂ))
        atTop
        (nhds
          ((cpRadialDifference 3
            (criticalDisplacement s.re) : ℝ) : ℂ))).mul hbudget
  have hpoint : ∀ M : ℕ,
      greenForm (𝕜 := ℂ)
            (finiteC3GenuineBracketGreenBoundaryPair (3 * M) s)
            (finiteC3GenuineBracketGreenBoundaryPair
              (3 * M) (reflectedParameter s)) +
          ((cpRadialDifference 3
            (criticalDisplacement s.re) : ℝ) : ℂ) *
            finiteCanonicalAngularGreenCorrection M s =
        ((cpRadialDifference 3
            (criticalDisplacement s.re) : ℝ) : ℂ) *
          (finiteReflectedGradientPairing (3 * M) s +
            finiteCanonicalAngularGreenCorrection M s) := by
    intro M
    rw [
      greenForm_finiteC3GenuineBracketGreenBoundaryPair_eq_radialFactorization]
    ring
  simpa only [hpoint, mul_zero] using hscaled

/-- The hoped-for rule "every Genuine zero closes the bracket-resolved C3
Green form" is exactly the existing strong nonvanishing frontier.  Thus the
finite factorization above is unconditional, while its zero-to-closure
activation cannot be smuggled in as a weaker bookkeeping lemma. -/
theorem genuineZeros_closeC3GenuineBracketGreenForm_iff_strongNonvanishing :
    (∀ {s : ℂ}, s ∈ genuineCriticalStrip →
      genuineContinuation s = 0 →
        Tendsto
          (fun M : ℕ ↦
            greenForm (𝕜 := ℂ)
              (finiteC3GenuineBracketGreenBoundaryPair M s)
              (finiteC3GenuineBracketGreenBoundaryPair M
                (reflectedParameter s)))
          atTop (nhds 0)) ↔
      GenuineStrongNonvanishingInStrip := by
  constructor
  · intro hclosure s hs hoff hzero
    have hre :=
      (greenForm_finiteC3GenuineBracketGreenBoundaryPair_tendsto_zero_iff
        hs).1 (hclosure hs hzero)
    exact hoff hre
  · intro hstrong s hs hzero
    apply
      (greenForm_finiteC3GenuineBracketGreenBoundaryPair_tendsto_zero_iff
        hs).2
    by_contra hoff
    exact (hstrong hs hoff) hzero

end

end NativeCarryC3Crosswalk
