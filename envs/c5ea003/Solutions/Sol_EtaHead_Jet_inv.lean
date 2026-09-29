-- Prove2me | solution 1 for EtaHead.Jet.inv
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:52:33.557673+00:00
-- url     : https://prove2.me/submissions/e445cd16-edfd-4249-8b0e-f672e43f08fd

-- Sol generated from Tropical/EtaQuotientHeadCoeff.lean
import Mathlib
import Definitions.Def_Tropical_EtaQuotientHeadCoeff

/-!
# The head coefficient of a normalised eta quotient

Let `a : ℕ → ℤ` be finitely supported (all our statements only use `a` on a finite
window, so finiteness is encoded by the truncation parameter `N`) and put

* `bCoeff a m = ∑_{k ∣ m} a k`,
* `etaQuotientProd a N = ∏_{m = 1}^{N} (1 - X^m)^{-bCoeff a m}`  (a unit of `ℤ⟦X⟧`).

If `∑ k · a k = 24` then the eta quotient `η_a = ∏_k η(kτ)^{a k}` satisfies
`η_a = q · ∏_m (1 - q^m)^{b m}`, hence

  `q / η_a = ∏_m (1 - q^m)^{-b m} = ∑_{n ≥ 0} c(n-1) qⁿ`,

so that in the usual "Hauptmodul" indexing `1/η_a = q^{-1} + c(0) + c(1) q + ⋯`
the head coefficient `c(1)` is the coefficient of `q²` in the product.

The main theorem `coeff_two_etaQuotientProd` proves

  `c(1) = a₁(a₁+3)/2 + a₂`,

for every truncation `N ≥ 2` (in particular the value is independent of `N`, which
is exactly the statement that the infinite product is well defined in degree `≤ 2`).

The proof is organised through a small amount of *2-jet* machinery: the group
homomorphism-like calculus of the coefficients in degrees `≤ 2` of units of `ℤ⟦X⟧`
with constant term `1` (`Jet`, `Jet.mul`, `Jet.inv`, `Jet.zpow`).

Further results in this file:

* `coeff_one_etaQuotientProd` : `c(0) = a₁`.
* `constantCoeff_etaQuotientProd` : the product is normalised, `c(-1) = 1`.
* `coeff_two_etaQuotientProd_stable` : the value of `c(1)` does not depend on the
  truncation `N ≥ 2`.

Companion files:

* `Tropical.EtaQuotientHeadStructure` : the Heisenberg cocycle `headCoeff_add`,
  the divisor regrouping `eta_regrouping_jet`, the Diophantine characterisation
  `pure_headCoeff_iff_sq`, surjectivity `headCoeff_surjective`, and the classical
  value `324` for `1/Δ` (`coeff_two_delta`).
* `Tropical.EtaQuotientSecondCoeff` : the 3-jet calculus and the closed form for
  `c(2)`.
* `Tropical.EtaQuotientStability` : all coefficients stabilise in the truncation.
-/

open EtaHead

open PowerSeries Finset

/-! ## Triangular numbers on `ℤ` -/






/-! ## 2-jets of power series -/


lemma coeff_one_mul (f g : PowerSeries ℤ) :
    coeff 1 (f * g) = coeff 0 f * coeff 1 g + coeff 1 f * coeff 0 g := by
  rw [coeff_mul]; simp [Finset.antidiagonal]

lemma coeff_two_mul (f g : PowerSeries ℤ) :
    coeff 2 (f * g) =
      coeff 0 f * coeff 2 g + coeff 1 f * coeff 1 g + coeff 2 f * coeff 0 g := by
  rw [coeff_mul]; simp [Finset.antidiagonal]; ring










/-! ## The basic units `1 - X^m` -/








/-! ## Divisor sums and the eta quotient product -/













open EtaHead in
theorem solution{u : (PowerSeries ℤ)ˣ} {c1 c2 : ℤ} (hu : Jet (u : PowerSeries ℤ) c1 c2) :
    Jet ((u⁻¹ : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) (-c1) (c1 ^ 2 - c2) := by
  obtain ⟨hu0, hu1, hu2⟩ := hu
  have hmul : (u : PowerSeries ℤ) * (u⁻¹ : (PowerSeries ℤ)ˣ) = 1 := u.mul_inv
  have h0 : constantCoeff ((u⁻¹ : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = 1 := by
    have := congrArg constantCoeff hmul
    rw [map_mul, hu0, map_one, one_mul] at this
    exact this
  have hu0' : coeff 0 (u : PowerSeries ℤ) = 1 := by
    rw [coeff_zero_eq_constantCoeff_apply]; exact hu0
  have h0' : coeff 0 ((u⁻¹ : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = 1 := by
    rw [coeff_zero_eq_constantCoeff_apply]; exact h0
  have e1 : coeff 1 ((u⁻¹ : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = -c1 := by
    have := congrArg (fun f => coeff 1 f) hmul
    simp only [coeff_one_mul, hu0', h0', hu1] at this
    simp [PowerSeries.coeff_one] at this
    linarith
  have e2 : coeff 2 ((u⁻¹ : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = c1 ^ 2 - c2 := by
    have := congrArg (fun f => coeff 2 f) hmul
    simp only [coeff_two_mul, hu0', h0', hu1, hu2, e1] at this
    simp [PowerSeries.coeff_one] at this
    nlinarith [this]
  exact ⟨h0, e1, e2⟩
