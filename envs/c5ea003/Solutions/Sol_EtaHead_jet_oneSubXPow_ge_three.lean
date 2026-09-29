-- Prove2me | solution 1 for EtaHead.jet_oneSubXPow_ge_three
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:54:02.600162+00:00
-- url     : https://prove2.me/submissions/50f9e0d2-2f16-461c-afc2-130f31275991

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













/-! ## The basic units `1 - X^m` -/



lemma coe_oneSubXPow {m : ℕ} (hm : 1 ≤ m) :
    ((oneSubXPow m : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) = 1 - X ^ m := by
  rw [oneSubXPow, dif_pos hm]
  rfl

lemma coeff_one_sub_X_pow (j m : ℕ) :
    coeff j (1 - X ^ m : PowerSeries ℤ)
      = (if j = 0 then 1 else 0) - (if j = m then 1 else 0) := by
  rw [map_sub, coeff_X_pow]
  simp [PowerSeries.coeff_one]




/-! ## Divisor sums and the eta quotient product -/













open EtaHead in
theorem solution{m : ℕ} (hm : 3 ≤ m) :
    Jet ((oneSubXPow m : (PowerSeries ℤ)ˣ) : PowerSeries ℤ) 0 0 := by
  have hm1 : 1 ≤ m := by omega
  rw [coe_oneSubXPow hm1]
  refine ⟨?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_one_sub_X_pow 0 m]
    have : ¬ (0 = m) := by omega
    simp [this]
  · rw [coeff_one_sub_X_pow 1 m]
    have : ¬ (1 = m) := by omega
    simp [this]
  · rw [coeff_one_sub_X_pow 2 m]
    have : ¬ (2 = m) := by omega
    simp [this]
