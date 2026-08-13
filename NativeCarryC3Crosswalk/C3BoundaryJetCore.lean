import NativeCarrySpectralWeyl.Camera.BracketSeries

/-!
# Analytic core of the C3 fifth-order oriented boundary jet

This module deliberately depends only on the spectral-Weyl side.  Keeping the
derivative layer separate prevents unrelated real-module instances in the
integration dependencies from changing elaboration of `HasDerivAt`.
-/

namespace NativeCarryC3Crosswalk

open NativeCarrySpectralWeyl.Camera

noncomputable section

/-- Coefficient of the `order`-th spatial derivative of `x ↦ x⁻ˢ`. -/
def dirichletSpaceCoefficient (s : ℂ) : ℕ → ℂ
  | 0 => 1
  | order + 1 =>
      dirichletSpaceCoefficient s order * (-s - (order : ℂ))

@[simp] theorem dirichletSpaceCoefficient_zero (s : ℂ) :
    dirichletSpaceCoefficient s 0 = 1 := rfl

@[simp] theorem dirichletSpaceCoefficient_succ (s : ℂ) (order : ℕ) :
    dirichletSpaceCoefficient s (order + 1) =
      dirichletSpaceCoefficient s order * (-s - (order : ℂ)) := rfl

/-- Closed form of one spatial derivative of the positive-real kernel. -/
def dirichletKernelHigherDeriv
    (order : ℕ) (s : ℂ) (x : ℝ) : ℂ :=
  dirichletSpaceCoefficient s order *
    (x : ℂ) ^ (-s - (order : ℂ))

@[simp] theorem dirichletKernelHigherDeriv_zero (s : ℂ) (x : ℝ) :
    dirichletKernelHigherDeriv 0 s x = dirichletKernel s x := by
  simp [dirichletKernelHigherDeriv, dirichletKernel]

/-- A constant multiple of a positive-real complex power has the expected derivative. -/
theorem const_mul_ofReal_cpow_hasDerivAt
    (coefficient exponent : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt
      (fun y : ℝ => coefficient * (y : ℂ) ^ exponent)
      (coefficient * (exponent * (x : ℂ) ^ (exponent - 1))) x := by
  by_cases hexponent : exponent = 0
  · rw [hexponent]
    simpa using hasDerivAt_const x coefficient
  · have hpow :=
      hasDerivAt_ofReal_cpow_const hx.ne' hexponent
    have hmul :=
      (hasDerivAt_const x coefficient).mul hpow
    simp only [zero_mul, zero_add] at hmul
    exact hmul

/-- The next recurrent closed form is exactly the derivative value above. -/
theorem dirichletKernelHigherDeriv_succ_apply
    (order : ℕ) (s : ℂ) (x : ℝ) :
    dirichletKernelHigherDeriv (order + 1) s x =
      dirichletSpaceCoefficient s order * (-s - (order : ℂ)) *
        (x : ℂ) ^ (-s - (order : ℂ) - 1) := by
  unfold dirichletKernelHigherDeriv
  rw [dirichletSpaceCoefficient_succ]
  have hshift :
      -s - ((order + 1 : ℕ) : ℂ) = -s - (order : ℂ) - 1 := by
    push_cast
    ring
  rw [hshift]

/-- Spatial point at which the first omitted C3 tail is expanded. -/
def c3BoundaryCenter (cutoff : ℕ) : ℝ :=
  3 * (cutoff + 1)

theorem c3BoundaryCenter_pos (cutoff : ℕ) :
    0 < c3BoundaryCenter cutoff := by
  unfold c3BoundaryCenter
  positivity

/--
Fifth-order oriented Euler--Maclaurin boundary jet used by the C3 ledgers:

`-F'(C)/3 + F''(C)/2 - 5F'''(C)/18 + F''''(C)/24 + F'''''(C)/60`.
-/
def c3OrientedBoundaryJet (cutoff : ℕ) (s : ℂ) : ℂ :=
  -(dirichletKernelHigherDeriv 1 s (c3BoundaryCenter cutoff)) / 3
    + dirichletKernelHigherDeriv 2 s (c3BoundaryCenter cutoff) / 2
    - 5 * dirichletKernelHigherDeriv 3 s (c3BoundaryCenter cutoff) / 18
    + dirichletKernelHigherDeriv 4 s (c3BoundaryCenter cutoff) / 24
    + dirichletKernelHigherDeriv 5 s (c3BoundaryCenter cutoff) / 60

end

end NativeCarryC3Crosswalk
