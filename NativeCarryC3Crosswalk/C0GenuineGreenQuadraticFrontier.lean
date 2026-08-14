import NativeCarryC3Crosswalk.C0GenuineGreenBoundaryIdentity
import CPFormal.Analytic.CpGenuineFirstOrthogonalGreenLimit
import CPFormal.Analytic.CpRadialCoercivity

/-!
# Quadratic C0--Genuine / Green frontier

The nonzero vertical factor `C0` transports the scalar Genuine readout, while
the reflected Green identity supplies an independent radial defect.  This
module keeps those two quantities as orthogonal quadratic channels:

`completed energy = normSq (C0 * Genuine) + radial Green defect ^ 2`.

The identity and its quantitative lower bound hold before any zero is
assumed.  They prove that the *completed* readout cannot vanish off the
half-abscissa.  They deliberately do not infer that the scalar Genuine
coordinate is nonzero: at a hypothetical off-critical Genuine zero, all
completed energy lies in the Green coordinate.  Thus the module records the
strongest non-circular consequence of the existing quadratic and Green
identities without identifying two distinct kernels.
-/

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp

noncomputable section

/-- The real infinite Green defect in one prime camera. -/
def c0GenuineGreenRadialDefect (p : ℕ) (s : ℂ) : ℝ :=
  cpRadialDifference p (criticalDisplacement s.re) *
    infiniteReflectedGreenEnergy s

/-- Orthogonal quadratic energy of the C0-dressed Genuine coordinate and one
prime Green coordinate. -/
def c0GenuineGreenCompletedEnergy (p : ℕ) (s : ℂ) : ℝ :=
  Complex.normSq (genuineCentralContinuationC2 s) +
    c0GenuineGreenRadialDefect p s ^ 2

/-- The scalar quadratic coordinate is exactly the nonzero C0 dressing times
the Genuine quadratic coordinate. -/
theorem normSq_genuineCentralContinuationC2_eq_c0_mul_genuine
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    Complex.normSq (genuineCentralContinuationC2 s) =
      Complex.normSq (c0VerticalFactor s) *
        Complex.normSq (genuineContinuation s) := by
  rw [genuineCentralContinuationC2_eq hs, Complex.normSq_mul]
  rfl

/-- Exact two-channel sum-of-squares ledger, valid before zeros. -/
theorem c0GenuineGreenCompletedEnergy_eq_sum_of_squares
    (p : ℕ) {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    c0GenuineGreenCompletedEnergy p s =
      Complex.normSq (c0VerticalFactor s) *
          Complex.normSq (genuineContinuation s) +
        c0GenuineGreenRadialDefect p s ^ 2 := by
  unfold c0GenuineGreenCompletedEnergy
  rw [normSq_genuineCentralContinuationC2_eq_c0_mul_genuine hs]

/-- The completed energy is nonnegative without a strip hypothesis. -/
theorem c0GenuineGreenCompletedEnergy_nonneg (p : ℕ) (s : ℂ) :
    0 ≤ c0GenuineGreenCompletedEnergy p s := by
  unfold c0GenuineGreenCompletedEnergy
  exact add_nonneg (Complex.normSq_nonneg _) (sq_nonneg _)

/-- Strict positivity of the reflected energy makes the one-camera Green
defect vanish exactly at zero critical displacement. -/
theorem c0GenuineGreenRadialDefect_eq_zero_iff
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    c0GenuineGreenRadialDefect p s = 0 ↔
      criticalDisplacement s.re = 0 := by
  unfold c0GenuineGreenRadialDefect
  have henergy : infiniteReflectedGreenEnergy s ≠ 0 :=
    ne_of_gt (infiniteReflectedGreenEnergy_pos hs)
  constructor
  · intro hzero
    have hradial :
        cpRadialDifference p (criticalDisplacement s.re) = 0 :=
      (mul_eq_zero.mp hzero).resolve_right henergy
    exact (cpRadialDifference_eq_zero_iff
      p hp (criticalDisplacement s.re)).mp hradial
  · intro hcritical
    rw [(cpRadialDifference_eq_zero_iff
      p hp (criticalDisplacement s.re)).2 hcritical, zero_mul]

/-- Exact kernel of the completed quadratic ledger.  Both coordinates must
vanish; no implication from the scalar coordinate to the Green coordinate is
inserted. -/
theorem c0GenuineGreenCompletedEnergy_eq_zero_iff
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    c0GenuineGreenCompletedEnergy p s = 0 ↔
      genuineContinuation s = 0 ∧ criticalDisplacement s.re = 0 := by
  constructor
  · intro hzero
    have hnorm : Complex.normSq (genuineCentralContinuationC2 s) = 0 := by
      have hnormNonneg :=
        Complex.normSq_nonneg (genuineCentralContinuationC2 s)
      have hdefectNonneg := sq_nonneg (c0GenuineGreenRadialDefect p s)
      unfold c0GenuineGreenCompletedEnergy at hzero
      nlinarith
    have hdefectSq : c0GenuineGreenRadialDefect p s ^ 2 = 0 := by
      have hnormNonneg :=
        Complex.normSq_nonneg (genuineCentralContinuationC2 s)
      have hdefectNonneg := sq_nonneg (c0GenuineGreenRadialDefect p s)
      unfold c0GenuineGreenCompletedEnergy at hzero
      nlinarith
    have hdefect : c0GenuineGreenRadialDefect p s = 0 := by
      nlinarith [sq_nonneg (c0GenuineGreenRadialDefect p s)]
    exact ⟨
      (genuineCentralContinuationC2_eq_zero_iff hs).mp
        (Complex.normSq_eq_zero.mp hnorm),
      (c0GenuineGreenRadialDefect_eq_zero_iff p hp hs).mp hdefect⟩
  · rintro ⟨hgenuine, hcritical⟩
    have hcentral : genuineCentralContinuationC2 s = 0 :=
      (genuineCentralContinuationC2_eq_zero_iff hs).2 hgenuine
    have hdefect : c0GenuineGreenRadialDefect p s = 0 :=
      (c0GenuineGreenRadialDefect_eq_zero_iff p hp hs).2 hcritical
    simp [c0GenuineGreenCompletedEnergy, hcentral, hdefect]

/-- Coordinate form of the completed kernel. -/
theorem c0GenuineGreenCompletedEnergy_eq_zero_iff_re_eq_half
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    c0GenuineGreenCompletedEnergy p s = 0 ↔
      genuineContinuation s = 0 ∧ s.re = (1 : ℝ) / 2 := by
  rw [c0GenuineGreenCompletedEnergy_eq_zero_iff p hp hs]
  constructor
  · rintro ⟨hzero, hcritical⟩
    refine ⟨hzero, ?_⟩
    unfold criticalDisplacement at hcritical
    linarith
  · rintro ⟨hzero, hhalf⟩
    refine ⟨hzero, ?_⟩
    unfold criticalDisplacement
    linarith

/-- Quantitative coercivity of the completed channel.  The lower bound is
entirely radial and is independent of the scalar Genuine value. -/
theorem c0GenuineGreenCompletedEnergy_ge_radial_coercive_square
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    (2 * |criticalDisplacement s.re| * Real.log p *
        infiniteReflectedGreenEnergy s) ^ 2 ≤
      c0GenuineGreenCompletedEnergy p s := by
  let delta : ℝ := criticalDisplacement s.re
  let energy : ℝ := infiniteReflectedGreenEnergy s
  let radial : ℝ := cpRadialDifference p delta
  have henergy : 0 < energy := by
    simpa [energy] using infiniteReflectedGreenEnergy_pos hs
  have hradial : 2 * |delta| * Real.log p ≤ |radial| := by
    simpa [delta, radial] using abs_cpRadialDifference_ge p hp delta
  have hmag :
      2 * |delta| * Real.log p * energy ≤ |radial * energy| := by
    have h := mul_le_mul_of_nonneg_right hradial henergy.le
    simpa [abs_mul, abs_of_pos henergy] using h
  have hlower : 0 ≤ 2 * |delta| * Real.log p * energy := by
    have hlog : 0 < Real.log p := by
      apply Real.log_pos
      exact_mod_cast hp.one_lt
    positivity
  have hsq :
      (2 * |delta| * Real.log p * energy) ^ 2 ≤
        (radial * energy) ^ 2 := by
    have := (sq_le_sq₀ hlower (abs_nonneg (radial * energy))).2 hmag
    calc
      (2 * |delta| * Real.log p * energy) ^ 2 ≤
          |radial * energy| ^ 2 := this
      _ = (radial * energy) ^ 2 := sq_abs (radial * energy)
  unfold c0GenuineGreenCompletedEnergy c0GenuineGreenRadialDefect
  dsimp [delta, energy, radial] at hsq ⊢
  nlinarith [Complex.normSq_nonneg (genuineCentralContinuationC2 s)]

/-- Off the half-abscissa the completed quadratic channel has strictly
positive energy, with no Genuine-zero hypothesis. -/
theorem c0GenuineGreenCompletedEnergy_pos_of_re_ne_half
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    0 < c0GenuineGreenCompletedEnergy p s := by
  have hne : c0GenuineGreenCompletedEnergy p s ≠ 0 := by
    intro hzero
    exact hoff
      ((c0GenuineGreenCompletedEnergy_eq_zero_iff_re_eq_half
        p hp hs).1 hzero).2
  exact (lt_iff_le_and_ne).2
    ⟨c0GenuineGreenCompletedEnergy_nonneg p s, Ne.symm hne⟩

/-- At a scalar Genuine zero, the completed energy is exactly the Green
defect square.  This is an identity, not a contradiction. -/
theorem c0GenuineGreenCompletedEnergy_eq_greenDefect_sq_of_genuine_zero
    (p : ℕ) {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    c0GenuineGreenCompletedEnergy p s =
      c0GenuineGreenRadialDefect p s ^ 2 := by
  have hcentral : genuineCentralContinuationC2 s = 0 :=
    (genuineCentralContinuationC2_eq_zero_iff hs).2 hzero
  simp [c0GenuineGreenCompletedEnergy, hcentral]

/-- Consequently, a hypothetical off-critical scalar Genuine zero carries
strictly positive completed energy entirely in the Green leg.  The theorem
pinpoints why positivity of the completed norm alone is not scalar
confinement. -/
theorem c0GenuineGreenCompletedEnergy_pos_of_genuine_zero_off_critical
    (p : ℕ) (hp : Nat.Prime p)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (_hzero : genuineContinuation s = 0)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    0 < c0GenuineGreenCompletedEnergy p s :=
  c0GenuineGreenCompletedEnergy_pos_of_re_ne_half p hp hs hoff

/-! ## Exact scope of the missing scalar-to-completed arrow -/

/-- The concrete assertion that every scalar Genuine zero also annihilates
the C3 completed quadratic energy.  It is named only to audit its logical
strength; no instance is declared. -/
def GenuineZerosCloseC0GenuineGreenCompletedEnergy : Prop :=
  ∀ {s : ℂ}, genuineContinuation s = 0 →
    s ∈ genuineCriticalStrip →
      c0GenuineGreenCompletedEnergy 3 s = 0

/-- Closing the completed quadratic channel at every scalar Genuine zero is
not supplied by the sum-of-squares identity: it is exactly strong
off-critical nonvanishing.  This equivalence is the circularity firewall for
any attempted use of the quadratic norm as scalar confinement. -/
theorem genuineZerosCloseC0GenuineGreenCompletedEnergy_iff_strongNonvanishing :
    GenuineZerosCloseC0GenuineGreenCompletedEnergy ↔
      GenuineStrongNonvanishingInStrip := by
  constructor
  · intro hclose s hs hoff hzero
    have henergy := hclose hzero hs
    exact hoff
      ((c0GenuineGreenCompletedEnergy_eq_zero_iff_re_eq_half
        3 (by norm_num) hs).1 henergy).2
  · intro hstrong s hzero hs
    apply (c0GenuineGreenCompletedEnergy_eq_zero_iff_re_eq_half
      3 (by norm_num) hs).2
    refine ⟨hzero, ?_⟩
    by_contra hoff
    exact (hstrong hs hoff) hzero

end

end NativeCarryC3Crosswalk
