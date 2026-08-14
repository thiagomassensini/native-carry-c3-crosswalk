import NativeCarryC3Crosswalk.C3StationaryRoot
import NativeCarrySpectralWeyl.Camera.HigherDerivativeTail

/-!
# C3 stationary-ledger enclosure bridge

The external stationary-localization ledger obtains the finite-root signs by
comparing the corrected finite quantities with one limiting C3 chart.  This
module internalizes that exact architecture.  It fixes conservative rational
margins implied by the Arb ledger and proves that sound limiting-value and
finite-to-limit enclosures produce `C3StationaryIntervalCertificate`.

No Arb ball is treated as a Lean proof.  The remaining transcendental leaves
are visible as fields of `C3StationaryLedgerEnclosures`.
-/

namespace NativeCarryC3Crosswalk

open Set
open FiniteNativeCarryOperator
open NativeCarrySpectralWeyl.Camera

noncomputable section

/-! ## Concrete limiting C3 quantities -/

/-- Infinite C3 characteristic restricted to the native line. -/
def c3LimitingCharacteristic (time : ℝ) : ℂ :=
  bracketCharacteristic 3 (nativeLine time)

/-- Real two-coordinate presentation of the limiting C3 characteristic. -/
def c3LimitingRealResidual (time : ℝ) : Operator.RealPlane :=
  unpackComplex (c3LimitingCharacteristic time)

/-- First native-time derivative of the infinite C3 characteristic. -/
def c3LimitingCharacteristicVelocity (time : ℝ) : ℂ :=
  iteratedDeriv 1 c3LimitingCharacteristic time

/-- Real presentation of the limiting velocity. -/
def c3LimitingRealVelocity (time : ℝ) : Operator.RealPlane :=
  unpackComplex (c3LimitingCharacteristicVelocity time)

/-- Second native-time derivative of the infinite C3 characteristic. -/
def c3LimitingCharacteristicAcceleration (time : ℝ) : ℂ :=
  iteratedDeriv 2 c3LimitingCharacteristic time

/-- Real presentation of the limiting acceleration. -/
def c3LimitingRealAcceleration (time : ℝ) : Operator.RealPlane :=
  unpackComplex (c3LimitingCharacteristicAcceleration time)

/-- Limiting stationary numerator `H∞ = A∞ · B∞`. -/
def c3LimitingStationaryNumerator (time : ℝ) : ℝ :=
  Operator.realDot (c3LimitingRealResidual time)
    (c3LimitingRealVelocity time)

/-- Limiting stationary slope in the same product-rule form as the finite slope. -/
def c3LimitingStationarySlope (time : ℝ) : ℝ :=
  Operator.realDot (c3LimitingRealVelocity time)
      (c3LimitingRealVelocity time) +
    Operator.realDot (c3LimitingRealResidual time)
      (c3LimitingRealAcceleration time)

/-! ## Exact conservative margins extracted from the ledger -/

/-- Common conservative endpoint margin: `9e-15`. -/
def c3LedgerEndpointMargin : ℝ := 9 / 10 ^ 15

/-- Uniform stationary perturbation cap: `1e-15`. -/
def c3LedgerStationaryError : ℝ := 1 / 10 ^ 15

/-- Conservative limiting slope margin. -/
def c3LedgerSlopeMargin : ℝ := 21

/-- Uniform slope perturbation cap: `1e-12`. -/
def c3LedgerSlopeError : ℝ := 1 / 10 ^ 12

/-- The stationary perturbation cap is strictly smaller than the endpoint margin. -/
theorem c3LedgerStationaryError_lt_endpointMargin :
    c3LedgerStationaryError < c3LedgerEndpointMargin := by
  norm_num [c3LedgerStationaryError, c3LedgerEndpointMargin]

/-- The slope perturbation cap is strictly smaller than the limiting slope margin. -/
theorem c3LedgerSlopeError_lt_slopeMargin :
    c3LedgerSlopeError < c3LedgerSlopeMargin := by
  norm_num [c3LedgerSlopeError, c3LedgerSlopeMargin]

/-!
`C3StationaryLedgerEnclosures` is the precise kernel hand-off for the external
Arb ledger.  Its first three fields enclose the limiting stationary chart; its
last two fields enclose the corrected finite-to-limit perturbations uniformly
from the certified threshold onward.
-/

/-- Sound analytic enclosures represented by the C3 localization ledger. -/
structure C3StationaryLedgerEnclosures : Prop where
  limit_left :
    c3LimitingStationaryNumerator c3StationaryAnchorLower ≤
      -c3LedgerEndpointMargin
  limit_right :
    c3LedgerEndpointMargin ≤
      c3LimitingStationaryNumerator c3StationaryAnchorUpper
  limit_slope : ∀ time ∈
      Ioo c3StationaryAnchorLower c3StationaryAnchorUpper,
    c3LedgerSlopeMargin ≤ c3LimitingStationarySlope time
  stationary_error : ∀ cutoff,
    c3StationaryCertificateThreshold ≤ cutoff →
    ∀ time ∈ ({c3StationaryAnchorLower,
        c3StationaryAnchorUpper} : Set ℝ),
      |c3CorrectedStationaryNumerator cutoff time -
          c3LimitingStationaryNumerator time| ≤
        c3LedgerStationaryError
  slope_error : ∀ cutoff,
    c3StationaryCertificateThreshold ≤ cutoff →
    ∀ time ∈ Ioo c3StationaryAnchorLower c3StationaryAnchorUpper,
      |c3CorrectedStationarySlope cutoff time -
          c3LimitingStationarySlope time| ≤
        c3LedgerSlopeError

/-- The ledger enclosures force the corrected left-endpoint sign. -/
theorem c3CorrectedStationaryNumerator_left_neg_of_ledgerEnclosures
    (enclosures : C3StationaryLedgerEnclosures)
    {cutoff : ℕ} (hcutoff : c3StationaryCertificateThreshold ≤ cutoff) :
    c3CorrectedStationaryNumerator cutoff c3StationaryAnchorLower < 0 := by
  have herror := enclosures.stationary_error cutoff hcutoff
    c3StationaryAnchorLower (by simp)
  have hupper := (abs_le.mp herror).2
  have hmargin := c3LedgerStationaryError_lt_endpointMargin
  linarith [enclosures.limit_left]

/-- The ledger enclosures force the corrected right-endpoint sign. -/
theorem c3CorrectedStationaryNumerator_right_pos_of_ledgerEnclosures
    (enclosures : C3StationaryLedgerEnclosures)
    {cutoff : ℕ} (hcutoff : c3StationaryCertificateThreshold ≤ cutoff) :
    0 < c3CorrectedStationaryNumerator cutoff c3StationaryAnchorUpper := by
  have herror := enclosures.stationary_error cutoff hcutoff
    c3StationaryAnchorUpper (by simp)
  have hlower := (abs_le.mp herror).1
  have hmargin := c3LedgerStationaryError_lt_endpointMargin
  linarith [enclosures.limit_right]

/-- The ledger enclosures force the corrected stationary slope to stay positive. -/
theorem c3CorrectedStationarySlope_pos_of_ledgerEnclosures
    (enclosures : C3StationaryLedgerEnclosures)
    {cutoff : ℕ} (hcutoff : c3StationaryCertificateThreshold ≤ cutoff)
    {time : ℝ}
    (htime : time ∈ Ioo c3StationaryAnchorLower c3StationaryAnchorUpper) :
    0 < c3CorrectedStationarySlope cutoff time := by
  have herror := enclosures.slope_error cutoff hcutoff time htime
  have hlower := (abs_le.mp herror).1
  have hmargin := c3LedgerSlopeError_lt_slopeMargin
  linarith [enclosures.limit_slope time htime]

/--
Sound C3 ledger enclosures instantiate the exact stationary-root certificate.
-/
theorem C3StationaryLedgerEnclosures.toIntervalCertificate
    (enclosures : C3StationaryLedgerEnclosures) :
    C3StationaryIntervalCertificate where
  left_sign := fun _cutoff hcutoff =>
    c3CorrectedStationaryNumerator_left_neg_of_ledgerEnclosures
      enclosures hcutoff
  right_sign := fun _cutoff hcutoff =>
    c3CorrectedStationaryNumerator_right_pos_of_ledgerEnclosures
      enclosures hcutoff
  slope_pos := fun _cutoff hcutoff _time htime =>
    c3CorrectedStationarySlope_pos_of_ledgerEnclosures
      enclosures hcutoff htime

/-- Every sound ledger enclosure package produces the unique stationary family. -/
theorem existsUnique_c3CorrectedStationaryCenter_of_ledgerEnclosures
    (enclosures : C3StationaryLedgerEnclosures)
    {cutoff : ℕ} (hcutoff : c3StationaryCertificateThreshold ≤ cutoff) :
    ∃! time : ℝ,
      time ∈ Icc c3StationaryAnchorLower c3StationaryAnchorUpper ∧
        IsC3CorrectedStationaryCenter cutoff time :=
  existsUnique_c3CorrectedStationaryCenter
    enclosures.toIntervalCertificate hcutoff

end

end NativeCarryC3Crosswalk
