import CPFormal.Analytic.CpFinitePortWronskian
import CPFormal.Analytic.CpBracketGreenFlux
import NativeCarrySpectralWeyl.Boundary.GreenRelation

/-!
# Reflected C3 Green form as a boundary pullback

The reflected CP Green flux and the abstract boundary Green form were
formalized in different upstream packages.  This file identifies them at a
finite cutoff without inserting a zero, a critical-line hypothesis, or a
chosen inverse.

For the canonical camera `p = 3`, the two coordinates at every arithmetic
cell are

* the phase-normalized C3 block gradient;
* the undressed positive Dirichlet gradient.

Keeping all cells as orthogonal coordinates in `EuclideanSpace ℂ (Fin M)`
turns the finite reflected CP flux into literally the `greenForm` used by
`NativeCarrySpectralWeyl.Boundary.GreenRelation`.  Consequently, membership
of the direct and reflected port pairs in one Green-isotropic relation forces
the finite reflected flux to vanish.

The membership statement is deliberately left explicit.  Establishing it
from Genuine/C3 boundary closure is the remaining arithmetic boundary
transport; it is not assumed or hidden in the definition of the form.
-/

open scoped BigOperators ComplexConjugate

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp
open NativeCarrySpectralWeyl.Boundary

noncomputable section

/-- Finite orthogonal carrier for the C3 Green ports at cutoff `M`. -/
abbrev FiniteC3GreenBoundarySpace (M : ℕ) :=
  EuclideanSpace ℂ (Fin M)

/-- Direct C3 boundary pair before scalar synthesis.  The first coordinate is
the phase-normalized C3 block and the second is the horizontal gradient. -/
def finiteC3GreenBoundaryPair (M : ℕ) (s : ℂ) :
    FiniteC3GreenBoundarySpace M × FiniteC3GreenBoundarySpace M :=
  (WithLp.toLp 2 (fun n : Fin M ↦
      phaseNormalizedCpBlockGradient 3 s n),
    WithLp.toLp 2 (fun n : Fin M ↦
      positiveDirichletGradient s n))

@[simp] theorem finiteC3GreenBoundaryPair_fst_apply
    (M : ℕ) (s : ℂ) (n : Fin M) :
    (finiteC3GreenBoundaryPair M s).1 n =
      phaseNormalizedCpBlockGradient 3 s n :=
  rfl

@[simp] theorem finiteC3GreenBoundaryPair_snd_apply
    (M : ℕ) (s : ℂ) (n : Fin M) :
    (finiteC3GreenBoundaryPair M s).2 n =
      positiveDirichletGradient s n :=
  rfl

/-- Exact reflected-Green/boundary-form intertwiner at every finite cutoff.
The right-hand side is the already formalized oriented CP flux; the left-hand
side is the abstract Green form used for boundary relations. -/
theorem greenForm_finiteC3GreenBoundaryPair_eq_orientedFlux
    (M : ℕ) (s : ℂ) :
    greenForm
        (finiteC3GreenBoundaryPair M s)
        (finiteC3GreenBoundaryPair M (reflectedParameter s)) =
      finiteOrientedCpGreenFlux 3 M s := by
  rw [greenForm, PiLp.inner_apply, PiLp.inner_apply,
    ← Finset.sum_sub_distrib]
  simp only [finiteC3GreenBoundaryPair_fst_apply,
    finiteC3GreenBoundaryPair_snd_apply, RCLike.inner_apply']
  rw [Finset.sum_fin_eq_sum_range]
  unfold finiteOrientedCpGreenFlux finitePhaseNormalizedCpGreenFlux
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hlt : n < M := Finset.mem_range.mp hn
  simp [hlt]

/-- Concrete syzygy consequence: if the direct and reflected C3 port pairs
belong to the same Green-isotropic boundary relation, the reflected C3 flux
vanishes.  No division by a Genuine value occurs. -/
theorem finiteOrientedC3GreenFlux_eq_zero_of_isotropicBoundary
    (M : ℕ) (s : ℂ)
    (relation : GreenRelation ℂ (FiniteC3GreenBoundarySpace M))
    (hisotropic : IsGreenIsotropic relation)
    (hdirect : finiteC3GreenBoundaryPair M s ∈ relation)
    (hreflected :
      finiteC3GreenBoundaryPair M (reflectedParameter s) ∈ relation) :
    finiteOrientedCpGreenFlux 3 M s = 0 := by
  rw [← greenForm_finiteC3GreenBoundaryPair_eq_orientedFlux]
  exact isGreenIsotropic_green_identity hisotropic hdirect hreflected

/-- Maximal Green-isotropy supplies the same concrete C3 closure theorem. -/
theorem finiteOrientedC3GreenFlux_eq_zero_of_maximalIsotropicBoundary
    (M : ℕ) (s : ℂ)
    (relation : GreenRelation ℂ (FiniteC3GreenBoundarySpace M))
    (hmaximal : IsMaximalGreenIsotropic relation)
    (hdirect : finiteC3GreenBoundaryPair M s ∈ relation)
    (hreflected :
      finiteC3GreenBoundaryPair M (reflectedParameter s) ∈ relation) :
    finiteOrientedCpGreenFlux 3 M s = 0 :=
  finiteOrientedC3GreenFlux_eq_zero_of_isotropicBoundary M s relation
    (isMaximalGreenIsotropic_isGreenIsotropic hmaximal) hdirect hreflected

/-- A Genuine zero supplies the already-proved telescoping boundary.  If, at
every cutoff, its direct and reflected C3 port pairs also land in one
Green-isotropic relation, then the complete bracket-coupled C3 flux closes in
the limit.  This is the concrete no-division form of the desired syzygy. -/
theorem bracketCoupledC3GreenFlux_tendsto_zero_of_genuineZero_and_isotropy
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (relation : ∀ M : ℕ,
      GreenRelation ℂ (FiniteC3GreenBoundarySpace M))
    (hisotropic : ∀ M : ℕ, IsGreenIsotropic (relation M))
    (hdirect : ∀ M : ℕ,
      finiteC3GreenBoundaryPair M s ∈ relation M)
    (hreflected : ∀ M : ℕ,
      finiteC3GreenBoundaryPair M (reflectedParameter s) ∈ relation M) :
    Filter.Tendsto
      (fun M : ℕ ↦ finiteBracketCoupledCpGreenFlux 3 M s)
      Filter.atTop (nhds 0) := by
  have hboundary :=
    finiteBracketCoupledSignedBoundary_tendsto_zero_of_genuine_zero
      hs hzero
  have hpoint : ∀ M : ℕ,
      finiteBracketCoupledCpGreenFlux 3 M s =
        finiteBracketCoupledSignedBoundary M s := by
    intro M
    rw [finiteBracketCoupledCpGreenFlux_eq_oriented_add_boundary,
      finiteOrientedC3GreenFlux_eq_zero_of_isotropicBoundary
        M s (relation M) (hisotropic M) (hdirect M) (hreflected M)]
    simp
  simpa only [hpoint] using hboundary

/-- End-to-end finite-boundary consequence.  At a Genuine zero in the strip,
the explicit C3 isotropic-membership transport forces the radial coordinate
to be exactly `1 / 2`.  All analytic positivity and boundary telescoping come
from the pinned CPFormal theorems; the only new input is the displayed
relation membership for the concrete direct/reflected C3 ports. -/
theorem re_eq_half_of_genuineZero_and_isotropicC3Boundary
    {s : ℂ} (hs : s ∈ genuineCriticalStrip)
    (hzero : genuineContinuation s = 0)
    (relation : ∀ M : ℕ,
      GreenRelation ℂ (FiniteC3GreenBoundarySpace M))
    (hisotropic : ∀ M : ℕ, IsGreenIsotropic (relation M))
    (hdirect : ∀ M : ℕ,
      finiteC3GreenBoundaryPair M s ∈ relation M)
    (hreflected : ∀ M : ℕ,
      finiteC3GreenBoundaryPair M (reflectedParameter s) ∈ relation M) :
    s.re = (1 : ℝ) / 2 := by
  have hflux :=
    bracketCoupledC3GreenFlux_tendsto_zero_of_genuineZero_and_isotropy
      hs hzero relation hisotropic hdirect hreflected
  have hcritical :=
    criticalDisplacement_eq_zero_of_coupledFlux_tendsto_zero
      3 (by norm_num) hs hzero hflux
  unfold criticalDisplacement at hcritical
  linarith

end

end NativeCarryC3Crosswalk
