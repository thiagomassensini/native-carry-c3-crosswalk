import NativeCarryC3Crosswalk.C0GenuineGreenQuadraticFrontier
import NativeCarryC3Crosswalk.C3PositionalCompatibilityBridge
import NativeCarryC3Crosswalk.EnrichedTfvdPairTailClosure

/-!
# Positional branch / reflected-Green quadratic crosswalk

This module realizes the noncompensation route on the enriched nonlocal
carrier, before any zero or critical-line condition is imposed.

First, it strengthens the old equality-of-zero-loci into the exact signed
factorization

`branchDefect = - positiveTransfer * cpRadialDifference`.

It then keeps the real and imaginary coordinates of the tail-resolved
Genuine/TFVD pair orthogonal to the positional branch defect.  The resulting
three-dimensional real Hilbert readout has the exact Pythagorean energy

`transfer^2 * normSq(tailDefect) + (GreenEnergy * branchDefect)^2`.

The first summand is exactly the nonvanishing C3 dressing of the scalar
Genuine energy.  The second summand is the prior positional incompatibility,
seen in Green scale.  Hence the completed kernel is precisely

`Genuine = 0 and positional compatibility`.

At a tail/Genuine zero only the first two coordinates are forced to vanish;
annihilating the third is equivalent to the foundational positional
compatibility.  This is the exact scope guard: the Pythagorean construction
removes cancellation between the channels but does not infer that scalar
closure annihilates an independent orthogonal coordinate.
-/

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp
open CPFormal.Carry.Cp

noncomputable section

def branchToGreenTransferCoefficient
    (p : ℕ) (sigma : ℝ) : ℝ :=
  (p : ℝ) ^ (-criticalDisplacement sigma) *
    (1 - branchRatio p sigma)⁻¹

theorem branchToGreenTransferCoefficient_pos
    (p : ℕ) (hp : Nat.Prime p)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    0 < branchToGreenTransferCoefficient p sigma := by
  unfold branchToGreenTransferCoefficient
  have hpow : 0 < (p : ℝ) ^ (-criticalDisplacement sigma) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _
  have hden : 0 < 1 - branchRatio p sigma := sub_pos.mpr
    (branchRatio_lt_one p hp hsigma)
  exact mul_pos hpow (inv_pos.mpr hden)

theorem branchDefect_eq_neg_transfer_mul_radialDifference
    (p : ℕ) (hp : Nat.Prime p)
    {sigma : ℝ} (hsigma : 0 < sigma) :
    branchDefect p sigma =
      -branchToGreenTransferCoefficient p sigma *
        cpRadialDifference p (criticalDisplacement sigma) := by
  let P : ℝ := p
  let delta : ℝ := criticalDisplacement sigma
  let q : ℝ := branchRatio p sigma
  have hP : 0 < P := by
    dsimp [P]
    exact_mod_cast hp.pos
  have hq : q < 1 := by
    simpa [q] using branchRatio_lt_one p hp hsigma
  have hden : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq)
  have hpq : P * q = P ^ (-2 * delta) := by
    dsimp [P, q, delta, branchRatio, criticalDisplacement]
    calc
      (p : ℝ) * (p : ℝ) ^ (-2 * sigma) =
          (p : ℝ) ^ (1 : ℝ) * (p : ℝ) ^ (-2 * sigma) := by
            rw [Real.rpow_one]
      _ = (p : ℝ) ^ ((1 : ℝ) + (-2 * sigma)) := by
            rw [Real.rpow_add hP]
      _ = (p : ℝ) ^ (-2 * (sigma - (1 : ℝ) / 2)) := by
            congr 1
            ring
  have hnegpos : P ^ (-delta) * P ^ delta = 1 := by
    rw [← Real.rpow_add hP]
    simp
  have hnegneg : P ^ (-delta) * P ^ (-delta) = P ^ (-2 * delta) := by
    rw [← Real.rpow_add hP]
    congr 1
    ring
  rw [branchDefect, branchNormSq_eq_closed p hp hsigma]
  change ((p - 1 : ℕ) : ℝ) * q * (1 - q)⁻¹ - 1 =
    -(P ^ (-delta) * (1 - q)⁻¹) *
      (P ^ delta - P ^ (-delta))
  rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  change (P - 1) * q * (1 - q)⁻¹ - 1 =
    -(P ^ (-delta) * (1 - q)⁻¹) *
      (P ^ delta - P ^ (-delta))
  field_simp [hden]
  calc
    (P - 1) * q - (1 - q) = P * q - 1 := by ring
    _ = P ^ (-2 * delta) - 1 := by rw [hpq]
    _ = -(P ^ (-delta) * (P ^ delta - P ^ (-delta))) := by
      rw [mul_sub, hnegpos, hnegneg]
      ring

abbrev C0GenuineBranchCompletedSpace := EuclideanSpace ℝ (Fin 3)

def c0GenuineBranchCompletedReadout
    (p : ℕ) (s : ℂ) : C0GenuineBranchCompletedSpace :=
  let transfer := branchToGreenTransferCoefficient p s.re
  let central := genuineCentralContinuationC2 s
  let branch := infiniteReflectedGreenEnergy s * branchDefect p s.re
  WithLp.toLp 2 fun i =>
    if i = (0 : Fin 3) then transfer * central.re
    else if i = (1 : Fin 3) then transfer * central.im
    else branch

@[simp] theorem c0GenuineBranchCompletedReadout_zero_apply
    (p : ℕ) (s : ℂ) :
    c0GenuineBranchCompletedReadout p s (0 : Fin 3) =
      branchToGreenTransferCoefficient p s.re *
        (genuineCentralContinuationC2 s).re := by
  simp [c0GenuineBranchCompletedReadout]

@[simp] theorem c0GenuineBranchCompletedReadout_one_apply
    (p : ℕ) (s : ℂ) :
    c0GenuineBranchCompletedReadout p s (1 : Fin 3) =
      branchToGreenTransferCoefficient p s.re *
        (genuineCentralContinuationC2 s).im := by
  simp [c0GenuineBranchCompletedReadout]

@[simp] theorem c0GenuineBranchCompletedReadout_two_apply
    (p : ℕ) (s : ℂ) :
    c0GenuineBranchCompletedReadout p s (2 : Fin 3) =
      infiniteReflectedGreenEnergy s * branchDefect p s.re := by
  simp [c0GenuineBranchCompletedReadout,
    show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide]

theorem c0GenuineBranchCompletedReadout_inner_self
    (p : ℕ) (s : ℂ) :
    inner ℝ (c0GenuineBranchCompletedReadout p s)
        (c0GenuineBranchCompletedReadout p s) =
      branchToGreenTransferCoefficient p s.re ^ 2 *
          Complex.normSq (genuineCentralContinuationC2 s) +
        (infiniteReflectedGreenEnergy s * branchDefect p s.re) ^ 2 := by
  rw [PiLp.inner_apply]
  simp [c0GenuineBranchCompletedReadout, Fin.sum_univ_three,
    Complex.normSq_apply]
  ring

theorem branchTransfer_sq_mul_c0GenuineGreenCompletedEnergy
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    branchToGreenTransferCoefficient p s.re ^ 2 *
        c0GenuineGreenCompletedEnergy p s =
      branchToGreenTransferCoefficient p s.re ^ 2 *
          Complex.normSq (genuineCentralContinuationC2 s) +
        (infiniteReflectedGreenEnergy s * branchDefect p s.re) ^ 2 := by
  let transfer := branchToGreenTransferCoefficient p s.re
  let radial := cpRadialDifference p (criticalDisplacement s.re)
  let energy := infiniteReflectedGreenEnergy s
  let defect := branchDefect p s.re
  have hbranch : defect = -transfer * radial := by
    simpa [defect, transfer, radial] using
      branchDefect_eq_neg_transfer_mul_radialDifference
        p hp hs.1
  have hscaled : transfer * (radial * energy) = -(energy * defect) := by
    rw [hbranch]
    ring
  unfold c0GenuineGreenCompletedEnergy c0GenuineGreenRadialDefect
  change transfer ^ 2 *
      (Complex.normSq (genuineCentralContinuationC2 s) +
        (radial * energy) ^ 2) =
    transfer ^ 2 * Complex.normSq (genuineCentralContinuationC2 s) +
      (energy * defect) ^ 2
  calc
    transfer ^ 2 *
        (Complex.normSq (genuineCentralContinuationC2 s) +
          (radial * energy) ^ 2) =
      transfer ^ 2 * Complex.normSq (genuineCentralContinuationC2 s) +
        (transfer * (radial * energy)) ^ 2 := by ring
    _ = transfer ^ 2 * Complex.normSq (genuineCentralContinuationC2 s) +
        (energy * defect) ^ 2 := by rw [hscaled]; ring

theorem c0GenuineBranchCompletedReadout_inner_self_eq_scaled_completedEnergy
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    inner ℝ (c0GenuineBranchCompletedReadout p s)
        (c0GenuineBranchCompletedReadout p s) =
      branchToGreenTransferCoefficient p s.re ^ 2 *
        c0GenuineGreenCompletedEnergy p s := by
  rw [c0GenuineBranchCompletedReadout_inner_self]
  exact (branchTransfer_sq_mul_c0GenuineGreenCompletedEnergy p hp hs).symm

theorem c0GenuineBranchCompletedReadout_norm_sq_eq_scaled_completedEnergy
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    ‖c0GenuineBranchCompletedReadout p s‖ ^ 2 =
      branchToGreenTransferCoefficient p s.re ^ 2 *
        c0GenuineGreenCompletedEnergy p s := by
  rw [← real_inner_self_eq_norm_sq]
  exact
    c0GenuineBranchCompletedReadout_inner_self_eq_scaled_completedEnergy
      p hp hs

/-- The completed Hilbert readout controls the original positional branch
defect with coefficient one after the exact Green-energy scaling. -/
theorem branchDefectGreenEnergy_sq_le_completedReadout_norm_sq
    (p : ℕ) (s : ℂ) :
    (infiniteReflectedGreenEnergy s * branchDefect p s.re) ^ 2 ≤
      ‖c0GenuineBranchCompletedReadout p s‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq,
    c0GenuineBranchCompletedReadout_inner_self]
  have hscalar :
      0 ≤ branchToGreenTransferCoefficient p s.re ^ 2 *
        Complex.normSq (genuineCentralContinuationC2 s) :=
    mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
  linarith

theorem c0GenuineBranchCompletedReadout_eq_zero_iff
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    c0GenuineBranchCompletedReadout p s = 0 ↔
      genuineContinuation s = 0 ∧ branchDefect p s.re = 0 := by
  have htransfer : branchToGreenTransferCoefficient p s.re ≠ 0 :=
    ne_of_gt (branchToGreenTransferCoefficient_pos p hp hs.1)
  have henergy : infiniteReflectedGreenEnergy s ≠ 0 :=
    ne_of_gt (infiniteReflectedGreenEnergy_pos hs)
  constructor
  · intro hzero
    have hzeroCoord := congrArg
      (fun v : C0GenuineBranchCompletedSpace => v (0 : Fin 3)) hzero
    have honeCoord := congrArg
      (fun v : C0GenuineBranchCompletedSpace => v (1 : Fin 3)) hzero
    have htwoCoord := congrArg
      (fun v : C0GenuineBranchCompletedSpace => v (2 : Fin 3)) hzero
    simp only [c0GenuineBranchCompletedReadout_zero_apply,
      c0GenuineBranchCompletedReadout_one_apply,
      c0GenuineBranchCompletedReadout_two_apply, PiLp.zero_apply]
      at hzeroCoord honeCoord htwoCoord
    have hre : (genuineCentralContinuationC2 s).re = 0 :=
      (mul_eq_zero.mp hzeroCoord).resolve_left htransfer
    have him : (genuineCentralContinuationC2 s).im = 0 :=
      (mul_eq_zero.mp honeCoord).resolve_left htransfer
    have hcentral : genuineCentralContinuationC2 s = 0 := by
      apply Complex.ext
      · simpa using hre
      · simpa using him
    exact
      ⟨(genuineCentralContinuationC2_eq_zero_iff hs).1 hcentral,
        (mul_eq_zero.mp htwoCoord).resolve_left henergy⟩
  · rintro ⟨hgenuine, hdefect⟩
    have hcentral : genuineCentralContinuationC2 s = 0 :=
      (genuineCentralContinuationC2_eq_zero_iff hs).2 hgenuine
    ext i
    fin_cases i <;>
      simp [c0GenuineBranchCompletedReadout, hcentral, hdefect]

theorem c0GenuineBranchCompletedReadout_eq_zero_iff_genuine_and_compatible
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    c0GenuineBranchCompletedReadout p s = 0 ↔
      genuineContinuation s = 0 ∧
        C3PositionalGeometryCompatible s.re := by
  rw [c0GenuineBranchCompletedReadout_eq_zero_iff p hp hs]
  apply and_congr_right
  intro _hgenuine
  rw [c3PositionalGeometryCompatible_iff]
  constructor
  · intro hdefect
    have hcritical :=
      (branchDefect_eq_zero_iff_criticalDisplacement_eq_zero
        p hp hs.1).1 hdefect
    unfold criticalDisplacement at hcritical
    linarith
  · intro hhalf
    apply
      (branchDefect_eq_zero_iff_criticalDisplacement_eq_zero
        p hp hs.1).2
    unfold criticalDisplacement
    linarith

theorem c0GenuineBranchCompletedReadout_eq_zero_iff_compatible_of_genuine_zero
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    c0GenuineBranchCompletedReadout p s = 0 ↔
      C3PositionalGeometryCompatible s.re := by
  rw [c0GenuineBranchCompletedReadout_eq_zero_iff_genuine_and_compatible
    p hp hs, and_iff_right hzero]

theorem c0GenuineBranchCompletedReadout_eq_zero_iff_compatible_of_tailDefect_zero
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (htail :
      finiteC3EnrichedTfvdPairTailDefect M kappa omega s = 0) :
    c0GenuineBranchCompletedReadout p s = 0 ↔
      C3PositionalGeometryCompatible s.re := by
  have hzero : genuineContinuation s = 0 :=
    (finiteC3EnrichedTfvdPairTailDefect_eq_zero_iff_genuine_zero
      M hkappa omega homega hs).1 htail
  exact
    c0GenuineBranchCompletedReadout_eq_zero_iff_compatible_of_genuine_zero
      p hp hs hzero

/-! ## Direct enriched-tail completed readout -/

abbrev C3EnrichedTailBranchCompletedSpace := EuclideanSpace ℝ (Fin 3)

/-- Three orthogonal real coordinates: real/imaginary parts of the exact
tail-resolved enriched-pair defect, followed by the positional branch defect
in its reflected Green-energy scale. -/
def c3EnrichedTailBranchCompletedReadout
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (p : ℕ) (s : ℂ) : C3EnrichedTailBranchCompletedSpace :=
  let transfer := branchToGreenTransferCoefficient p s.re
  let tail := finiteC3EnrichedTfvdPairTailDefect M kappa omega s
  let branch := infiniteReflectedGreenEnergy s * branchDefect p s.re
  WithLp.toLp 2 fun i =>
    if i = (0 : Fin 3) then transfer * tail.re
    else if i = (1 : Fin 3) then transfer * tail.im
    else branch

@[simp] theorem c3EnrichedTailBranchCompletedReadout_zero_apply
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (p : ℕ) (s : ℂ) :
    c3EnrichedTailBranchCompletedReadout M kappa omega p s (0 : Fin 3) =
      branchToGreenTransferCoefficient p s.re *
        (finiteC3EnrichedTfvdPairTailDefect M kappa omega s).re := by
  simp [c3EnrichedTailBranchCompletedReadout]

@[simp] theorem c3EnrichedTailBranchCompletedReadout_one_apply
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (p : ℕ) (s : ℂ) :
    c3EnrichedTailBranchCompletedReadout M kappa omega p s (1 : Fin 3) =
      branchToGreenTransferCoefficient p s.re *
        (finiteC3EnrichedTfvdPairTailDefect M kappa omega s).im := by
  simp [c3EnrichedTailBranchCompletedReadout]

@[simp] theorem c3EnrichedTailBranchCompletedReadout_two_apply
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (p : ℕ) (s : ℂ) :
    c3EnrichedTailBranchCompletedReadout M kappa omega p s (2 : Fin 3) =
      infiniteReflectedGreenEnergy s * branchDefect p s.re := by
  simp [c3EnrichedTailBranchCompletedReadout,
    show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide]

/-- Exact Pythagorean ledger on the enriched nonlocal carrier. -/
theorem c3EnrichedTailBranchCompletedReadout_inner_self
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (p : ℕ) (s : ℂ) :
    inner ℝ (c3EnrichedTailBranchCompletedReadout M kappa omega p s)
        (c3EnrichedTailBranchCompletedReadout M kappa omega p s) =
      branchToGreenTransferCoefficient p s.re ^ 2 *
          Complex.normSq
            (finiteC3EnrichedTfvdPairTailDefect M kappa omega s) +
        (infiniteReflectedGreenEnergy s * branchDefect p s.re) ^ 2 := by
  rw [PiLp.inner_apply]
  simp [c3EnrichedTailBranchCompletedReadout, Fin.sum_univ_three,
    Complex.normSq_apply]
  ring

theorem c3EnrichedTailBranchCompletedReadout_norm_sq
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (p : ℕ) (s : ℂ) :
    ‖c3EnrichedTailBranchCompletedReadout M kappa omega p s‖ ^ 2 =
      branchToGreenTransferCoefficient p s.re ^ 2 *
          Complex.normSq
            (finiteC3EnrichedTfvdPairTailDefect M kappa omega s) +
        (infiniteReflectedGreenEnergy s * branchDefect p s.re) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  exact c3EnrichedTailBranchCompletedReadout_inner_self
    M kappa omega p s

/-- In the strip, the first two orthogonal coordinates are exactly the
nonvanishing C3 dressing of the scalar Genuine readout. -/
theorem c3EnrichedTailBranchCompletedReadout_norm_sq_eq_genuine_branch
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    (p : ℕ) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    ‖c3EnrichedTailBranchCompletedReadout M kappa omega p s‖ ^ 2 =
      branchToGreenTransferCoefficient p s.re ^ 2 *
          (Complex.normSq (cpChartFactor 3 s) *
            Complex.normSq (genuineContinuation s)) +
        (infiniteReflectedGreenEnergy s * branchDefect p s.re) ^ 2 := by
  rw [c3EnrichedTailBranchCompletedReadout_norm_sq,
    finiteC3EnrichedTfvdPairTailDefect_eq_neg_factor_mul_genuine
      M hkappa omega homega hs]
  simp only [Complex.normSq_neg, Complex.normSq_mul]

/-- The completed nonlocal readout is projectively independent of the finite
cutoff: its tail coordinate is already the complete bracket chart. -/
theorem c3EnrichedTailBranchCompletedReadout_cutoff_invariant
    (M N : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    (p : ℕ) {s : ℂ} (hs : -1 < s.re) :
    c3EnrichedTailBranchCompletedReadout M kappa omega p s =
      c3EnrichedTailBranchCompletedReadout N kappa omega p s := by
  have htail :
      finiteC3EnrichedTfvdPairTailDefect M kappa omega s =
        finiteC3EnrichedTfvdPairTailDefect N kappa omega s := by
    rw [finiteC3EnrichedTfvdPairTailDefect_eq_genuineTailGreenDefect
        M hkappa omega homega s,
      finiteC3EnrichedTfvdPairTailDefect_eq_genuineTailGreenDefect
        N hkappa omega homega s]
    exact finiteC3GenuineTailGreenDefect_cutoff_invariant M N hs
  ext i
  fin_cases i <;>
    simp [c3EnrichedTailBranchCompletedReadout, htail]

/-- Coercivity of the completed pair in the already existing positional
defect; no zero or critical-line hypothesis is used. -/
theorem branchDefectGreenEnergy_sq_le_enrichedTailCompletedReadout_norm_sq
    (M : ℕ) (kappa : ℂ) (omega : ℕ → ℂ)
    (p : ℕ) (s : ℂ) :
    (infiniteReflectedGreenEnergy s * branchDefect p s.re) ^ 2 ≤
      ‖c3EnrichedTailBranchCompletedReadout M kappa omega p s‖ ^ 2 := by
  rw [c3EnrichedTailBranchCompletedReadout_norm_sq]
  have htail :
      0 ≤ branchToGreenTransferCoefficient p s.re ^ 2 *
        Complex.normSq
          (finiteC3EnrichedTfvdPairTailDefect M kappa omega s) :=
    mul_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
  linarith

/-- Exact kernel of the enriched Pythagorean completed readout. -/
theorem c3EnrichedTailBranchCompletedReadout_eq_zero_iff
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    c3EnrichedTailBranchCompletedReadout M kappa omega p s = 0 ↔
      genuineContinuation s = 0 ∧ branchDefect p s.re = 0 := by
  have htransfer : branchToGreenTransferCoefficient p s.re ≠ 0 :=
    ne_of_gt (branchToGreenTransferCoefficient_pos p hp hs.1)
  have henergy : infiniteReflectedGreenEnergy s ≠ 0 :=
    ne_of_gt (infiniteReflectedGreenEnergy_pos hs)
  constructor
  · intro hzero
    have hzeroCoord := congrArg
      (fun v : C3EnrichedTailBranchCompletedSpace => v (0 : Fin 3)) hzero
    have honeCoord := congrArg
      (fun v : C3EnrichedTailBranchCompletedSpace => v (1 : Fin 3)) hzero
    have htwoCoord := congrArg
      (fun v : C3EnrichedTailBranchCompletedSpace => v (2 : Fin 3)) hzero
    simp only [c3EnrichedTailBranchCompletedReadout_zero_apply,
      c3EnrichedTailBranchCompletedReadout_one_apply,
      c3EnrichedTailBranchCompletedReadout_two_apply, PiLp.zero_apply]
      at hzeroCoord honeCoord htwoCoord
    have hre :
        (finiteC3EnrichedTfvdPairTailDefect M kappa omega s).re = 0 :=
      (mul_eq_zero.mp hzeroCoord).resolve_left htransfer
    have him :
        (finiteC3EnrichedTfvdPairTailDefect M kappa omega s).im = 0 :=
      (mul_eq_zero.mp honeCoord).resolve_left htransfer
    have htail : finiteC3EnrichedTfvdPairTailDefect M kappa omega s = 0 := by
      apply Complex.ext
      · simpa using hre
      · simpa using him
    exact
      ⟨(finiteC3EnrichedTfvdPairTailDefect_eq_zero_iff_genuine_zero
          M hkappa omega homega hs).1 htail,
        (mul_eq_zero.mp htwoCoord).resolve_left henergy⟩
  · rintro ⟨hgenuine, hdefect⟩
    have htail : finiteC3EnrichedTfvdPairTailDefect M kappa omega s = 0 :=
      (finiteC3EnrichedTfvdPairTailDefect_eq_zero_iff_genuine_zero
        M hkappa omega homega hs).2 hgenuine
    ext i
    fin_cases i <;>
      simp [c3EnrichedTailBranchCompletedReadout, htail, hdefect]

/-- Kernel phrased purely as scalar zero plus foundational positional
compatibility. -/
theorem c3EnrichedTailBranchCompletedReadout_eq_zero_iff_genuine_and_compatible
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    c3EnrichedTailBranchCompletedReadout M kappa omega p s = 0 ↔
      genuineContinuation s = 0 ∧
        C3PositionalGeometryCompatible s.re := by
  rw [c3EnrichedTailBranchCompletedReadout_eq_zero_iff
      M hkappa omega homega p hp hs]
  apply and_congr_right
  intro _hgenuine
  rw [c3PositionalGeometryCompatible_iff]
  constructor
  · intro hdefect
    have hcritical :=
      (branchDefect_eq_zero_iff_criticalDisplacement_eq_zero
        p hp hs.1).1 hdefect
    unfold criticalDisplacement at hcritical
    linarith
  · intro hhalf
    apply
      (branchDefect_eq_zero_iff_criticalDisplacement_eq_zero
        p hp hs.1).2
    unfold criticalDisplacement
    linarith

/-- The exact outcome of activating the tail/Genuine kernel: only the first
two completed coordinates are forced to zero; closing the last coordinate is
equivalent to positional compatibility. -/
theorem c3EnrichedTailBranchCompletedReadout_eq_zero_iff_compatible_of_tailDefect_zero
    (M : ℕ) {kappa : ℂ} (hkappa : kappa ≠ 0)
    (omega : ℕ → ℂ) (homega : ∀ m, omega m ≠ 0)
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (htail : finiteC3EnrichedTfvdPairTailDefect M kappa omega s = 0) :
    c3EnrichedTailBranchCompletedReadout M kappa omega p s = 0 ↔
      C3PositionalGeometryCompatible s.re := by
  have hzero : genuineContinuation s = 0 :=
    (finiteC3EnrichedTfvdPairTailDefect_eq_zero_iff_genuine_zero
      M hkappa omega homega hs).1 htail
  rw [c3EnrichedTailBranchCompletedReadout_eq_zero_iff_genuine_and_compatible
      M hkappa omega homega p hp hs,
    and_iff_right hzero]

end

end NativeCarryC3Crosswalk
