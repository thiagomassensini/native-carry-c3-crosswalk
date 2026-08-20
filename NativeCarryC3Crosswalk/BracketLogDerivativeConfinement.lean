import Mathlib.Analysis.Analytic.Order
import CPFormal.Analytic.CpGenuineRealAxisPositivity
import NativeCarryC3Crosswalk.BracketGlobalRelationalLaw

/-!
# Bracket log-derivative route to global confinement

The algebraic C2 tilt gives a signed transverse bracket.  The remaining global
question is whether the oscillatory carrier can compensate that signed field.
This module isolates a genuinely analytic way to rule out compensation.

If an independently constructed bracket log-derivative is analytic off the
critical line and satisfies

\[
  F' = -QF
\]

there, then F cannot vanish there.  The proof is by analytic order and handles
all finite multiplicities at once: a zero of order m makes F' have order
m - 1, while the analytic product QF has order at least m.

For the canonical Genuine continuation, finite analytic order in the whole
open critical strip is proved here, rather than assumed.  It follows from
holomorphy, connectedness of the strip, and the already proved nonvanishing on
the real segment.

The remaining construction target is therefore precise: identify the bracket
log-derivative with a regular Cauchy/Stieltjes (equivalently Herglotz-type)
readout off the real height axis and prove the differential identity.  No
simplicity assumption on a zero occurs in this route.
-/

open scoped Topology

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp
open Filter

noncomputable section

/-- The open Genuine strip is convex, hence preconnected. -/
theorem isPreconnected_genuineCriticalStrip :
    IsPreconnected genuineCriticalStrip := by
  have hconv : Convex ℝ genuineCriticalStrip := by
    intro z hz w hw a b ha hb hab
    simp only [genuineCriticalStrip, Set.mem_setOf_eq, Complex.add_re,
      Complex.smul_re, smul_eq_mul] at hz hw ⊢
    constructor
    · rcases eq_or_lt_of_le ha with rfl | haPos
      · have hbOne : b = 1 := by linarith
        simpa [hbOne] using hw.1
      · have hleft : 0 < a * z.re := mul_pos haPos hz.1
        have hright : 0 ≤ b * w.re :=
          mul_nonneg hb (le_of_lt hw.1)
        linarith
    · rcases eq_or_lt_of_le hb with rfl | hbPos
      · have haOne : a = 1 := by linarith
        simpa [haOne] using hz.2
      · have hleft : a * z.re ≤ a * 1 :=
          mul_le_mul_of_nonneg_left (le_of_lt hz.2) ha
        have hright : b * w.re < b * 1 :=
          mul_lt_mul_of_pos_left hw.2 hbPos
        linarith
  exact hconv.isPreconnected

/-- The canonical Genuine continuation has finite analytic order at every
point of the open critical strip.  This discharges the possible
locally-identically-zero branch before any log-derivative bridge is used. -/
theorem analyticOrderAt_genuineContinuation_ne_top
    {s : ℂ} (hs : s ∈ genuineCriticalStrip) :
    analyticOrderAt genuineContinuation s ≠ ⊤ := by
  let x : ℂ := ((1 / 2 : ℝ) : ℂ)
  have hx : x ∈ genuineCriticalStrip := by
    dsimp [x]
    constructor <;> norm_num
  have hxAnalytic : AnalyticAt ℂ genuineContinuation x :=
    analyticOnNhd_genuineContinuation_genuineCriticalStrip x hx
  have hxNe : genuineContinuation x ≠ 0 := by
    dsimp [x]
    exact genuineContinuation_ofReal_ne_zero
      (σ := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hxOrder : analyticOrderAt genuineContinuation x ≠ ⊤ := by
    rw [hxAnalytic.analyticOrderAt_eq_zero.mpr hxNe]
    simp
  exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
    analyticOnNhd_genuineContinuation_genuineCriticalStrip
    isPreconnected_genuineCriticalStrip hx hs hxOrder

/-- Analytic-order obstruction for a regular logarithmic derivative.

This is the multiplicity-independent core.  If F has finite analytic order
at z, Q is analytic there, and F' = -QF in a neighborhood, then F(z)
is nonzero. -/
theorem no_zero_of_regular_analytic_logDerivative
    {F Q : ℂ → ℂ} {z : ℂ}
    (hF : AnalyticAt ℂ F z)
    (hQ : AnalyticAt ℂ Q z)
    (hODE : deriv F =ᶠ[𝓝 z] -(Q * F))
    (hfinite : analyticOrderAt F z ≠ ⊤) :
    F z ≠ 0 := by
  intro hzero
  have horderNe : analyticOrderAt F z ≠ 0 :=
    (hF.analyticOrderAt_ne_zero).2 hzero
  have hcast :
      (analyticOrderNatAt F z : ℕ∞) = analyticOrderAt F z :=
    Nat.cast_analyticOrderNatAt hfinite
  have hmNe : analyticOrderNatAt F z ≠ 0 := by
    intro hm
    apply horderNe
    rw [← hcast, hm]
    simp
  have hmPos : 0 < analyticOrderNatAt F z :=
    Nat.pos_of_ne_zero hmNe
  let n := analyticOrderNatAt F z - 1
  have hmn : analyticOrderNatAt F z = n + 1 := by
    dsimp [n]
    omega
  have horder :
      analyticOrderAt F z = ((n + 1 : ℕ) : ℕ∞) := by
    calc
      analyticOrderAt F z =
          (analyticOrderNatAt F z : ℕ∞) := hcast.symm
      _ = ((n + 1 : ℕ) : ℕ∞) := by rw [hmn]
  have hderiv :
      analyticOrderAt (deriv F) z = (n : ℕ∞) :=
    analyticOrderAt_deriv_of_pos hF horder
  have horders :
      analyticOrderAt (deriv F) z =
        analyticOrderAt Q z + analyticOrderAt F z := by
    calc
      analyticOrderAt (deriv F) z =
          analyticOrderAt (-(Q * F)) z :=
        analyticOrderAt_congr hODE
      _ = analyticOrderAt (Q * F) z := analyticOrderAt_neg
      _ = analyticOrderAt Q z + analyticOrderAt F z :=
        analyticOrderAt_mul hQ hF
  have heq :
      (n : ℕ∞) =
        analyticOrderAt Q z + ((n + 1 : ℕ) : ℕ∞) := by
    calc
      (n : ℕ∞) = analyticOrderAt (deriv F) z := hderiv.symm
      _ = analyticOrderAt Q z + analyticOrderAt F z := horders
      _ = analyticOrderAt Q z + ((n + 1 : ℕ) : ℕ∞) := by rw [horder]
  have hle : ((n + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by
    calc
      ((n + 1 : ℕ) : ℕ∞) ≤
          analyticOrderAt Q z + ((n + 1 : ℕ) : ℕ∞) :=
        self_le_add_left _ _
      _ = (n : ℕ∞) := heq.symm
  have hlt : (n : ℕ∞) < ((n + 1 : ℕ) : ℕ∞) := by
    exact_mod_cast Nat.lt_succ_self n
  exact (not_lt_of_ge hle) hlt

/-- Contrapositive form: at a finite-order zero, any function satisfying the
log-derivative identity must fail to be analytic at that point. -/
theorem regular_analytic_logDerivative_impossible_at_zero
    {F Q : ℂ → ℂ} {z : ℂ}
    (hF : AnalyticAt ℂ F z)
    (hfinite : analyticOrderAt F z ≠ ⊤)
    (hzero : F z = 0)
    (hODE : deriv F =ᶠ[𝓝 z] -(Q * F)) :
    ¬ AnalyticAt ℂ Q z := by
  intro hQ
  exact (no_zero_of_regular_analytic_logDerivative
    hF hQ hODE hfinite) hzero

/-- Exact interface to be supplied by the bracket/Stieltjes construction.
The log-derivative is required to be regular only off the critical line, and
the differential identity is local there. -/
structure RegularBracketLogDerivativeBridge where
  logarithmicDerivative : ℂ → ℂ
  analyticAt_offCritical :
    ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
      s.re ≠ (1 : ℝ) / 2 →
        AnalyticAt ℂ logarithmicDerivative s
  differential_identity :
    ∀ {s : ℂ}, s ∈ genuineCriticalStrip →
      s.re ≠ (1 : ℝ) / 2 →
        deriv genuineContinuation =ᶠ[𝓝 s]
          -(logarithmicDerivative * genuineContinuation)

/-- A regular bracket log-derivative excludes every Genuine zero off the
critical line, without a root-simplicity hypothesis. -/
theorem genuineContinuation_ne_zero_offCritical_of_regularBracketLogDerivative
    (bridge : RegularBracketLogDerivativeBridge)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hoff : s.re ≠ (1 : ℝ) / 2) :
    genuineContinuation s ≠ 0 := by
  exact no_zero_of_regular_analytic_logDerivative
    (analyticOnNhd_genuineContinuation_genuineCriticalStrip s hs)
    (bridge.analyticAt_offCritical hs hoff)
    (bridge.differential_identity hs hoff)
    (analyticOrderAt_genuineContinuation_ne_top hs)

/-- Zero-confinement form of the log-derivative route. -/
theorem genuineZero_re_eq_half_of_regularBracketLogDerivative
    (bridge : RegularBracketLogDerivativeBridge)
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0) :
    s.re = (1 : ℝ) / 2 := by
  by_contra hoff
  exact
    (genuineContinuation_ne_zero_offCritical_of_regularBracketLogDerivative
      bridge hs hoff) hzero

/-- The regular bracket log-derivative bridge closes the existing global
strong-nonvanishing target. -/
theorem genuineStrongNonvanishingInStrip_of_regularBracketLogDerivative
    (bridge : RegularBracketLogDerivativeBridge) :
    GenuineStrongNonvanishingInStrip := by
  intro s hs hoff
  exact
    genuineContinuation_ne_zero_offCritical_of_regularBracketLogDerivative
      bridge hs hoff

/-- Consequently the differentiated C3 Green bracket closes at every Genuine
zero.  This connects the analytic-order route to the relational law. -/
theorem genuineZerosCloseC3GenuineBracketGreenForm_of_regularBracketLogDerivative
    (bridge : RegularBracketLogDerivativeBridge) :
    GenuineZerosCloseC3GenuineBracketGreenForm := by
  exact
    genuineZerosCloseC3GenuineBracketGreenForm_iff_strongNonvanishing.mpr
      (genuineStrongNonvanishingInStrip_of_regularBracketLogDerivative bridge)

end

end NativeCarryC3Crosswalk
