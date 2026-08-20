import CPFormal.Analytic.CpFinitePortWronskian
import CPFormal.Analytic.CpFiniteTfvdLogJetGreenComparison

/-!
# Polarized two-variable C3 Green--gamma identity

This module formalizes the exact part of the two-variable C3 proposal without
identifying it prematurely with the completed Genuine logarithmic derivative.

For two independent parameters, the raw C3 block is the camera eigenvalue
`3^(-s)` multiplying the horizontal Dirichlet gradient.  Polarizing the
Green pairing therefore factors it as the eigenvalue difference times a
positive Gram kernel.

The final declarations also retain two already-proved obstructions to the
completed scalar identification: scalar synthesis has a nontrivial
off-diagonal sector, and the logarithmic jet is not universally absorbed by
the raw Green channel.
-/

open scoped BigOperators

namespace NativeCarryC3Crosswalk

open CPFormal.Analytic.Cp

noncomputable section

/-- Raw C3 camera eigenvalue at a complex parameter. -/
def c3RawCameraEigenvalue (s : ℂ) : ℂ :=
  natDirichletTerm s 3

/-- Polarized Gram kernel of the finite horizontal C3 gradients. -/
def c3RawGammaGram (M : ℕ) (r s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range M,
    (starRingEnd ℂ) (positiveDirichletGradient r n) *
      positiveDirichletGradient s n

/-- Polarized Green pairing of the raw C3 port
`(cpBlockGradient 3, positiveDirichletGradient)`. -/
def c3RawGreenPairing (M : ℕ) (r s : ℂ) : ℂ :=
  ∑ n ∈ Finset.range M,
    ((starRingEnd ℂ) (positiveDirichletGradient r n) *
        cpBlockGradient 3 s n -
      (starRingEnd ℂ) (cpBlockGradient 3 r n) *
        positiveDirichletGradient s n)

/-- Exact two-variable C3 Green--gamma factorization.  It is cross-multiplied,
so no division or removable-singularity side condition is introduced. -/
theorem c3RawGreenPairing_eq_eigenvalueDifference_mul_gammaGram
    (M : ℕ) (r s : ℂ) :
    c3RawGreenPairing M r s =
      (c3RawCameraEigenvalue s -
          (starRingEnd ℂ) (c3RawCameraEigenvalue r)) *
        c3RawGammaGram M r s := by
  unfold c3RawGreenPairing c3RawCameraEigenvalue c3RawGammaGram
  calc
    (∑ n ∈ Finset.range M,
      ((starRingEnd ℂ) (positiveDirichletGradient r n) *
          cpBlockGradient 3 s n -
        (starRingEnd ℂ) (cpBlockGradient 3 r n) *
          positiveDirichletGradient s n)) =
        ∑ n ∈ Finset.range M,
          ((natDirichletTerm s 3 -
              (starRingEnd ℂ) (natDirichletTerm r 3)) *
            ((starRingEnd ℂ) (positiveDirichletGradient r n) *
              positiveDirichletGradient s n)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [cpBlockGradient_eq_eigenvalue_mul,
        cpBlockGradient_eq_eigenvalue_mul]
      simp only [map_mul]
      ring
    _ = (natDirichletTerm s 3 -
          (starRingEnd ℂ) (natDirichletTerm r 3)) *
        ∑ n ∈ Finset.range M,
          ((starRingEnd ℂ) (positiveDirichletGradient r n) *
            positiveDirichletGradient s n) := by
      rw [Finset.mul_sum]

/-- Height-coordinate parameter `s(z)=1/2+i z`. -/
def c3RawHeightParameter (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) + Complex.I * z

/-- The same exact factorization in two independent height variables. -/
theorem c3RawHeightGreenPairing_eq_eigenvalueDifference_mul_gammaGram
    (M : ℕ) (w z : ℂ) :
    c3RawGreenPairing M
        (c3RawHeightParameter w) (c3RawHeightParameter z) =
      (c3RawCameraEigenvalue (c3RawHeightParameter z) -
          (starRingEnd ℂ)
            (c3RawCameraEigenvalue (c3RawHeightParameter w))) *
        c3RawGammaGram M
          (c3RawHeightParameter w) (c3RawHeightParameter z) :=
  c3RawGreenPairing_eq_eigenvalueDifference_mul_gammaGram
    M (c3RawHeightParameter w) (c3RawHeightParameter z)

/-- Positive diagonal energy underlying the raw C3 Gram kernel. -/
def c3RawGammaEnergy (M : ℕ) (s : ℂ) : ℝ :=
  ∑ n ∈ Finset.range M, ‖positiveDirichletGradient s n‖ ^ 2

/-- The raw C3 diagonal Gram energy is nonnegative at every finite cutoff. -/
theorem c3RawGammaEnergy_nonneg (M : ℕ) (s : ℂ) :
    0 ≤ c3RawGammaEnergy M s := by
  unfold c3RawGammaEnergy
  positivity

/-- The logarithmic-jet channel cannot be replaced universally by the raw C3
Green channel; the mismatch is already nonzero at the first edge. -/
theorem c3LogJetChannel_not_absorbed_by_rawGreen_at_zero :
    canonicalReflectedLogJetEdgeWedge 0 0 ≠
      canonicalOrientedCpGreenEdge 3 0 0 :=
  canonicalReflectedLogJetEdgeWedge_ne_green_at_zero 3

/-- Scalar synthesis cannot universally be identified with the
provenance-preserving diagonal Green pairing. -/
theorem c3ScalarSynthesis_not_universally_greenDiagonal :
    finiteScalarPortWronskian 2
        (fun _ ↦ 0)
        (fun m ↦ if m = 0 then (1 : ℂ) else 0)
        (fun n ↦ if n = 1 then (1 : ℂ) else 0)
        (fun _ ↦ 0) ≠
      finiteDiagonalPortWronskian 2
        (fun _ ↦ 0)
        (fun m ↦ if m = 0 then (1 : ℂ) else 0)
        (fun n ↦ if n = 1 then (1 : ℂ) else 0)
        (fun _ ↦ 0) :=
  finiteScalarPortWronskian_ne_diagonal_witness

end

end NativeCarryC3Crosswalk
