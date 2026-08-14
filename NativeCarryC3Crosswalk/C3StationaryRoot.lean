import NativeCarryC3Crosswalk.C3StationarySlope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-!
# C3 corrected stationary-root family

This module internalizes the exact threshold and rational anchor interval from
the C3 stationary-localization ledger.  It proves the complete promotion from
endpoint signs and a positive stationary slope to a unique corrected center,
and selects the resulting family without using a floating-point center.

The three interval-enclosure fields remain explicit: the external Arb ledger
has not yet been turned into kernel proofs of those concrete inequalities.
-/

namespace NativeCarryC3Crosswalk

open Set

noncomputable section

/-- Certified cutoff threshold recorded by the stationary-localization ledger. -/
def c3StationaryCertificateThreshold : ℕ := 131072

/-- Exact rational lower endpoint of the anchor interval. -/
def c3StationaryAnchorLower : ℝ :=
  92.491899270558483805857220904387963299360620986373

/-- Exact rational upper endpoint of the anchor interval. -/
def c3StationaryAnchorUpper : ℝ :=
  92.491899270558484805857220904387963299360620986373

/-- The two exact rational endpoints are strictly ordered. -/
theorem c3StationaryAnchorLower_lt_upper :
    c3StationaryAnchorLower < c3StationaryAnchorUpper := by
  norm_num [c3StationaryAnchorLower, c3StationaryAnchorUpper]

/--
Kernel-facing form of the concrete C3 interval certificate.

Unlike a generic root contract, every function, cutoff threshold, and endpoint
is fixed here to the corrected C3 construction.  An inhabitant must prove the
two endpoint signs and the positive slope on the exact ledger interval for
every cutoff at or above `131072`.
-/
structure C3StationaryIntervalCertificate : Prop where
  left_sign : ∀ cutoff, c3StationaryCertificateThreshold ≤ cutoff →
    c3CorrectedStationaryNumerator cutoff c3StationaryAnchorLower < 0
  right_sign : ∀ cutoff, c3StationaryCertificateThreshold ≤ cutoff →
    0 < c3CorrectedStationaryNumerator cutoff c3StationaryAnchorUpper
  slope_pos : ∀ cutoff, c3StationaryCertificateThreshold ≤ cutoff →
    ∀ time ∈ Ioo c3StationaryAnchorLower c3StationaryAnchorUpper,
      0 < c3CorrectedStationarySlope cutoff time

/-- A concrete interval certificate makes `h_M` strictly increasing. -/
theorem c3CorrectedStationaryNumerator_strictMonoOn
    (certificate : C3StationaryIntervalCertificate)
    {cutoff : ℕ} (hcutoff : c3StationaryCertificateThreshold ≤ cutoff) :
    StrictMonoOn (c3CorrectedStationaryNumerator cutoff)
      (Icc c3StationaryAnchorLower c3StationaryAnchorUpper) := by
  apply strictMonoOn_of_deriv_pos
    (convex_Icc c3StationaryAnchorLower c3StationaryAnchorUpper)
  · exact (continuous_c3CorrectedStationaryNumerator cutoff).continuousOn
  · intro time htime
    rw [interior_Icc] at htime
    rw [deriv_c3CorrectedStationaryNumerator]
    exact certificate.slope_pos cutoff hcutoff time htime

/--
Every certified cutoff has exactly one corrected stationary center in the
exact anchor interval.
-/
theorem existsUnique_c3CorrectedStationaryCenter
    (certificate : C3StationaryIntervalCertificate)
    {cutoff : ℕ} (hcutoff : c3StationaryCertificateThreshold ≤ cutoff) :
    ∃! time : ℝ,
      time ∈ Icc c3StationaryAnchorLower c3StationaryAnchorUpper ∧
        IsC3CorrectedStationaryCenter cutoff time := by
  have hordered : c3StationaryAnchorLower ≤ c3StationaryAnchorUpper :=
    c3StationaryAnchorLower_lt_upper.le
  have hcontinuous : ContinuousOn (c3CorrectedStationaryNumerator cutoff)
      (Icc c3StationaryAnchorLower c3StationaryAnchorUpper) :=
    (continuous_c3CorrectedStationaryNumerator cutoff).continuousOn
  have hzero :
      (0 : ℝ) ∈ Icc
        (c3CorrectedStationaryNumerator cutoff c3StationaryAnchorLower)
        (c3CorrectedStationaryNumerator cutoff c3StationaryAnchorUpper) :=
    ⟨(certificate.left_sign cutoff hcutoff).le,
      (certificate.right_sign cutoff hcutoff).le⟩
  rcases intermediate_value_Icc hordered hcontinuous hzero with
    ⟨time, htime, hstationary⟩
  have hmono :=
    c3CorrectedStationaryNumerator_strictMonoOn certificate hcutoff
  refine ⟨time, ⟨htime, hstationary⟩, ?_⟩
  intro other hother
  exact hmono.injOn hother.1 htime (by
    rw [hother.2, hstationary])

/--
The corrected stationary center selected from the kernel theorem.  Below the
certified threshold the definition uses the lower endpoint; no theorem treats
that default value as a stationary center.
-/
def correctedStationaryCenter
    (certificate : C3StationaryIntervalCertificate) (cutoff : ℕ) : ℝ :=
  if hcutoff : c3StationaryCertificateThreshold ≤ cutoff then
    Classical.choose
      (existsUnique_c3CorrectedStationaryCenter certificate hcutoff).exists
  else
    c3StationaryAnchorLower

/-- The selected center lies in the exact anchor interval above the threshold. -/
theorem correctedStationaryCenter_mem
    (certificate : C3StationaryIntervalCertificate)
    {cutoff : ℕ} (hcutoff : c3StationaryCertificateThreshold ≤ cutoff) :
    correctedStationaryCenter certificate cutoff ∈
      Icc c3StationaryAnchorLower c3StationaryAnchorUpper := by
  rw [correctedStationaryCenter, dif_pos hcutoff]
  exact (Classical.choose_spec
    (existsUnique_c3CorrectedStationaryCenter certificate hcutoff).exists).1

/-- The selected center solves the corrected stationary equation exactly. -/
theorem correctedStationaryCenter_isStationary
    (certificate : C3StationaryIntervalCertificate)
    {cutoff : ℕ} (hcutoff : c3StationaryCertificateThreshold ≤ cutoff) :
    IsC3CorrectedStationaryCenter cutoff
      (correctedStationaryCenter certificate cutoff) := by
  rw [correctedStationaryCenter, dif_pos hcutoff]
  exact (Classical.choose_spec
    (existsUnique_c3CorrectedStationaryCenter certificate hcutoff).exists).2

/-- The selected center is the only stationary point in the anchor interval. -/
theorem correctedStationaryCenter_unique
    (certificate : C3StationaryIntervalCertificate)
    {cutoff : ℕ} (hcutoff : c3StationaryCertificateThreshold ≤ cutoff)
    {time : ℝ}
    (htime : time ∈ Icc c3StationaryAnchorLower c3StationaryAnchorUpper)
    (hstationary : IsC3CorrectedStationaryCenter cutoff time) :
    time = correctedStationaryCenter certificate cutoff := by
  apply (existsUnique_c3CorrectedStationaryCenter certificate hcutoff).unique
  · exact ⟨htime, hstationary⟩
  · exact ⟨correctedStationaryCenter_mem certificate hcutoff,
      correctedStationaryCenter_isStationary certificate hcutoff⟩

/-- Corrected core residual evaluated on the selected stationary family. -/
def c3StationaryCoreError
    (certificate : C3StationaryIntervalCertificate) (cutoff : ℕ) : ℝ :=
  c3CorrectedCoreError cutoff (correctedStationaryCenter certificate cutoff)

/-- The stationary core-error family is nonnegative. -/
theorem c3StationaryCoreError_nonneg
    (certificate : C3StationaryIntervalCertificate) (cutoff : ℕ) :
    0 ≤ c3StationaryCoreError certificate cutoff :=
  c3CorrectedCoreError_nonneg cutoff
    (correctedStationaryCenter certificate cutoff)

end

end NativeCarryC3Crosswalk
