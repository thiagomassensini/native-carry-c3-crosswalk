import NativeCarryC3Crosswalk.EnrichedTfvdPairTailClosure
import CPFormal.Analytic.CpGenuineKernelPrimeState

/-!
# Genuine control of the existing quadratic carry energy

This module does not introduce another norm.  It tests the proposed
noncompensation route against the prime-camera Hilbert norm already built in
`CPFormal`.

At every nonempty Green cutoff, the energy of a single prime camera vanishes
exactly when the old quadratic branch defect vanishes.  Thus the lower,
coercive leg of the desired estimate is already complete.

The remaining upper leg would have to make the scalar Genuine readout control
that existing energy.  We state the most direct coefficient-one inequality
and audit its exact strength at a Genuine zero.  Lean proves that it holds
there exactly at `Re s = 1 / 2`; requiring it at every Genuine zero is
equivalent to the existing strong-nonvanishing frontier.  Consequently the
inequality is a precise target, not a consequence silently supplied by the
current Green or Pythagorean identities.

The final section performs the same audit for uniform finite-prime-atlas
control.  Off the half-abscissa, every proposed scalar majorant is violated by
some finite atlas.  This is the concrete obstruction to obtaining the missing
upper bound merely by changing the order of summation.
-/

open scoped BigOperators

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp

noncomputable section

/-! ## The existing norm already detects the quadratic branch defect -/

/-- At a nonempty cutoff, the energy of one prime-camera state vanishes
exactly when the original quadratic branch defect vanishes.  No Genuine-zero
hypothesis occurs. -/
theorem primeGreenBulkSingletonEnergy_eq_zero_iff_branchDefect_eq_zero
    (M : ℕ) (hM : 0 < M) (p : Nat.Primes)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    ‖primeGreenBulkFiniteState M s {p}‖ ^ 2 = 0 ↔
      branchDefect p s.re = 0 := by
  rw [primeGreenBulkFiniteState_norm_sq]
  simp only [Finset.sum_singleton]
  constructor
  · intro hsq
    have hprofile : primeCarryGreenBulkCutoffProfile M s p = 0 := by
      nlinarith [sq_nonneg (primeCarryGreenBulkCutoffProfile M s p)]
    rw [primeCarryGreenBulkCutoffProfile_eq] at hprofile
    unfold primeCarryGreenRadialProfile at hprofile
    have hamplitude : primeCarryAmplitudeRatio p ≠ 0 :=
      ne_of_gt (primeCarryAmplitudeRatio_pos p p.prop.one_le)
    have henergy : (finiteReflectedGradientPairing M s).re ≠ 0 :=
      ne_of_gt (finiteReflectedGradientPairing_re_pos hM hs)
    have hradial :
        cpRadialDifference p (criticalDisplacement s.re) = 0 := by
      rcases mul_eq_zero.mp hprofile with hleft | hright
      · exact (mul_eq_zero.mp hleft).resolve_left hamplitude
      · exact (henergy hright).elim
    have hcritical : criticalDisplacement s.re = 0 :=
      (cpRadialDifference_eq_zero_iff
        p p.prop (criticalDisplacement s.re)).1 hradial
    exact
      (branchDefect_eq_zero_iff_criticalDisplacement_eq_zero
        p p.prop hs.1).2 hcritical
  · intro hdefect
    have hcritical : criticalDisplacement s.re = 0 :=
      (branchDefect_eq_zero_iff_criticalDisplacement_eq_zero
        p p.prop hs.1).1 hdefect
    rw [primeCarryGreenBulkCutoffProfile_eq]
    simp [primeCarryGreenRadialProfile, hcritical, cpRadialDifference]

/-- The same singleton energy has the unique zero `Re s = 1 / 2`. -/
theorem primeGreenBulkSingletonEnergy_eq_zero_iff_re_eq_half
    (M : ℕ) (hM : 0 < M) (p : Nat.Primes)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    ‖primeGreenBulkFiniteState M s {p}‖ ^ 2 = 0 ↔
      s.re = (1 : ℝ) / 2 := by
  rw [primeGreenBulkSingletonEnergy_eq_zero_iff_branchDefect_eq_zero
      M hM p hs,
    branchDefect_eq_zero_iff_criticalDisplacement_eq_zero
      p p.prop hs.1]
  unfold criticalDisplacement
  constructor <;> intro h <;> linarith

/-! ## Direct scalar-to-energy control -/

/-- The direct coefficient-one estimate suggested by noncompensation: the
existing single-camera Hilbert energy is controlled by the squared Genuine
readout.  This is a proposition to be proved, not an assumed bridge. -/
def GenuineReadoutControlsSingletonCarryEnergyAt
    (M : ℕ) (p : Nat.Primes) (s : ℂ) : Prop :=
  ‖primeGreenBulkFiniteState M s {p}‖ ^ 2 ≤
    Complex.normSq (cpChartFactor 3 s * genuineContinuation s)

/-- At a Genuine zero, the proposed direct estimate holds exactly at the
quadratic equilibrium.  The forward direction uses only nonnegativity of the
existing Hilbert norm; the reverse direction uses its already-proved unique
zero. -/
theorem genuineReadoutControlsSingletonCarryEnergyAt_iff_re_eq_half_of_zero
    (M : ℕ) (hM : 0 < M) (p : Nat.Primes)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    GenuineReadoutControlsSingletonCarryEnergyAt M p s ↔
      s.re = (1 : ℝ) / 2 := by
  unfold GenuineReadoutControlsSingletonCarryEnergyAt
  rw [hzero]
  simp only [mul_zero, map_zero]
  constructor
  · intro henergy
    have hzeroEnergy : ‖primeGreenBulkFiniteState M s {p}‖ ^ 2 = 0 := by
      have hnonneg : 0 ≤ ‖primeGreenBulkFiniteState M s {p}‖ ^ 2 :=
        sq_nonneg _
      linarith
    exact
      (primeGreenBulkSingletonEnergy_eq_zero_iff_re_eq_half
        M hM p hs).1 hzeroEnergy
  · intro hre
    have hzeroEnergy : ‖primeGreenBulkFiniteState M s {p}‖ ^ 2 = 0 :=
      (primeGreenBulkSingletonEnergy_eq_zero_iff_re_eq_half
        M hM p hs).2 hre
    rw [hzeroEnergy]

/-- Coercive version of the proposed estimate: an arbitrary strictly positive
coefficient is allowed in front of the existing carry energy.  This matches
the usual `kappa * energy ≤ normSq readout` formulation without weakening the
kernel consequence. -/
def GenuineReadoutCoercivelyControlsSingletonCarryEnergyAt
    (M : ℕ) (p : Nat.Primes) (s : ℂ) : Prop :=
  ∃ kappa : ℝ, 0 < kappa ∧
    kappa * ‖primeGreenBulkFiniteState M s {p}‖ ^ 2 ≤
      Complex.normSq (cpChartFactor 3 s * genuineContinuation s)

/-- Even after allowing an arbitrary positive coercivity coefficient, at a
Genuine zero the estimate holds exactly at quadratic equilibrium. -/
theorem genuineReadoutCoercivelyControlsSingletonCarryEnergyAt_iff_re_eq_half_of_zero
    (M : ℕ) (hM : 0 < M) (p : Nat.Primes)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    GenuineReadoutCoercivelyControlsSingletonCarryEnergyAt M p s ↔
      s.re = (1 : ℝ) / 2 := by
  constructor
  · rintro ⟨kappa, hkappa, hcontrol⟩
    rw [hzero] at hcontrol
    simp only [mul_zero, map_zero] at hcontrol
    have hnonneg : 0 ≤ ‖primeGreenBulkFiniteState M s {p}‖ ^ 2 :=
      sq_nonneg _
    have hzeroEnergy : ‖primeGreenBulkFiniteState M s {p}‖ ^ 2 = 0 := by
      nlinarith
    exact
      (primeGreenBulkSingletonEnergy_eq_zero_iff_re_eq_half
        M hM p hs).1 hzeroEnergy
  · intro hre
    refine ⟨1, zero_lt_one, ?_⟩
    have hzeroEnergy : ‖primeGreenBulkFiniteState M s {p}‖ ^ 2 = 0 :=
      (primeGreenBulkSingletonEnergy_eq_zero_iff_re_eq_half
        M hM p hs).2 hre
    rw [hzeroEnergy, hzero]
    norm_num

/-- Global form of the direct energy-control target. -/
def GenuineZerosControlSingletonCarryEnergy
    (M : ℕ) (p : Nat.Primes) : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    genuineContinuation s = 0 →
      GenuineReadoutControlsSingletonCarryEnergyAt M p s

/-- Requiring the direct estimate at all Genuine zeros has exactly the
strength of the already isolated strong-nonvanishing statement.  In
particular, this theorem prevents the desired upper estimate from being
mistaken for a consequence of the existing Pythagorean identity. -/
theorem genuineZerosControlSingletonCarryEnergy_iff_strongNonvanishing
    (M : ℕ) (hM : 0 < M) (p : Nat.Primes) :
    GenuineZerosControlSingletonCarryEnergy M p ↔
      GenuineStrongNonvanishingInStrip := by
  constructor
  · intro hcontrol s hs hoff hzero
    have hre :=
      (genuineReadoutControlsSingletonCarryEnergyAt_iff_re_eq_half_of_zero
        M hM p hs hzero).1 (hcontrol hs hzero)
    exact hoff hre
  · intro hstrong s hs hzero
    apply
      (genuineReadoutControlsSingletonCarryEnergyAt_iff_re_eq_half_of_zero
        M hM p hs hzero).2
    by_contra hoff
    exact (hstrong hs hoff) hzero

/-- Global form of the positive-coefficient coercive target. -/
def GenuineZerosHaveCoerciveSingletonCarryEnergyControl
    (M : ℕ) (p : Nat.Primes) : Prop :=
  ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
    genuineContinuation s = 0 →
      GenuineReadoutCoercivelyControlsSingletonCarryEnergyAt M p s

/-- Allowing the coercivity coefficient to depend on the zero does not make
the missing kernel transport weaker: globally it is still exactly strong
nonvanishing off the half-abscissa. -/
theorem genuineZerosHaveCoerciveSingletonCarryEnergyControl_iff_strongNonvanishing
    (M : ℕ) (hM : 0 < M) (p : Nat.Primes) :
    GenuineZerosHaveCoerciveSingletonCarryEnergyControl M p ↔
      GenuineStrongNonvanishingInStrip := by
  constructor
  · intro hcontrol s hs hoff hzero
    have hre :=
      (genuineReadoutCoercivelyControlsSingletonCarryEnergyAt_iff_re_eq_half_of_zero
        M hM p hs hzero).1 (hcontrol hs hzero)
    exact hoff hre
  · intro hstrong s hs hzero
    apply
      (genuineReadoutCoercivelyControlsSingletonCarryEnergyAt_iff_re_eq_half_of_zero
        M hM p hs hzero).2
    by_contra hoff
    exact (hstrong hs hoff) hzero

/-! ## Uniform atlas control and its exact obstruction -/

/-- A finite scalar Genuine readout uniformly controls the already-existing
prime-camera Hilbert energies as the finite atlas grows.  The multiplier is
required to be nonnegative but is otherwise arbitrary. -/
def GenuineReadoutControlsPrimeGreenAtlasEnergyAt
    (M : ℕ) (s : ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ S : Finset Nat.Primes,
    ‖primeGreenBulkFiniteState M s S‖ ^ 2 ≤
      C * Complex.normSq (cpChartFactor 3 s * genuineContinuation s)

/-- Uniform atlas control by one scalar is possible exactly at zero radial
displacement.  This statement is independent of whether the scalar Genuine
readout itself vanishes. -/
theorem genuineReadoutControlsPrimeGreenAtlasEnergyAt_iff_critical
    (M : ℕ) (hM : 0 < M)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    GenuineReadoutControlsPrimeGreenAtlasEnergyAt M s ↔
      criticalDisplacement s.re = 0 := by
  constructor
  · rintro ⟨C, _hC, hcontrol⟩
    apply (primeGreenBulkFiniteStatesBounded_iff M hM hs).1
    exact
      ⟨C * Complex.normSq (cpChartFactor 3 s * genuineContinuation s),
        hcontrol⟩
  · intro hcritical
    refine ⟨0, le_rfl, ?_⟩
    intro S
    rw [primeGreenBulkFiniteState_norm_sq]
    have hprofile : ∀ p : Nat.Primes,
        primeCarryGreenBulkCutoffProfile M s p = 0 := by
      intro p
      rw [primeCarryGreenBulkCutoffProfile_eq]
      simp [primeCarryGreenRadialProfile, hcritical, cpRadialDifference]
    simp [hprofile]

/-- Equivalently, the scalar controls the atlas exactly when the original
quadratic branch norm is saturated. -/
theorem genuineReadoutControlsPrimeGreenAtlasEnergyAt_iff_branchNormSq
    (M : ℕ) (hM : 0 < M)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    GenuineReadoutControlsPrimeGreenAtlasEnergyAt M s ↔
      branchNormSq 3 s.re = 1 := by
  rw [genuineReadoutControlsPrimeGreenAtlasEnergyAt_iff_critical M hM hs,
    branchNormSq_eq_one_iff 3 (by norm_num) hs.1]
  unfold criticalDisplacement
  constructor <;> intro h <;> linarith

/-- Off the half-abscissa, every proposed finite scalar majorant is exceeded
by some finite prime atlas.  This is the exact quantitative obstruction to
the desired upper transport with the current scalar readout. -/
theorem exists_primeGreenAtlas_violating_scalar_majorant_of_re_ne_half
    (M : ℕ) (hM : 0 < M)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) (B : ℝ) :
    ∃ S : Finset Nat.Primes,
      B < ‖primeGreenBulkFiniteState M s S‖ ^ 2 := by
  by_contra hnot
  have hbound : ∀ S : Finset Nat.Primes,
      ‖primeGreenBulkFiniteState M s S‖ ^ 2 ≤ B := by
    intro S
    exact le_of_not_gt (fun hgt => hnot ⟨S, hgt⟩)
  have hbounded : PrimeGreenBulkFiniteStatesBounded M s := ⟨B, hbound⟩
  have hcritical :=
    (primeGreenBulkFiniteStatesBounded_iff M hM hs).1 hbounded
  apply hoff
  unfold criticalDisplacement at hcritical
  linarith

/-- In particular, no multiple of the scalar Genuine energy can uniformly
majorize the atlas off the half-abscissa. -/
theorem exists_primeGreenAtlas_violating_genuineReadout_majorant_of_re_ne_half
    (M : ℕ) (hM : 0 < M)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) (C : ℝ) :
    ∃ S : Finset Nat.Primes,
      C * Complex.normSq (cpChartFactor 3 s * genuineContinuation s) <
        ‖primeGreenBulkFiniteState M s S‖ ^ 2 :=
  exists_primeGreenAtlas_violating_scalar_majorant_of_re_ne_half
    M hM hs hoff
      (C * Complex.normSq (cpChartFactor 3 s * genuineContinuation s))

/-- The same obstruction, specialized to a hypothetical off-critical Genuine
zero: the scalar side is exactly zero while a finite atlas has positive
existing carry energy. -/
theorem exists_primeGreenAtlas_positive_energy_of_genuine_zero_off_critical
    (M : ℕ) (hM : 0 < M)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    ∃ S : Finset Nat.Primes,
      0 < ‖primeGreenBulkFiniteState M s S‖ ^ 2 := by
  simpa [hzero] using
    (exists_primeGreenAtlas_violating_genuineReadout_majorant_of_re_ne_half
      M hM hs hoff 1)

end

end NativeCarryC3Crosswalk
