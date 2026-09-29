-- Prove2me | Definitions.Def_Tropical_EtaQuotientHeadCoeff
-- name    : Tropical_EtaQuotientHeadCoeff
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:30:03.927373+00:00
-- url     : https://prove2.me/theorems/c1166335-7766-449b-b666-a8dc1f1ac038
-- title:
--   Aether Catalog definitions — Tropical_EtaQuotientHeadCoeff
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.EtaQuotientHeadCoeff`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/EtaQuotientHeadCoeff.lean by skeleton subtraction
import Mathlib

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

namespace EtaHead

open PowerSeries Finset

/-! ## Triangular numbers on `ℤ` -/

/-- `Tri n = n(n-1)/2`, the binomial coefficient `C(n,2)` extended to all integers. -/
def Tri (n : ℤ) : ℤ := n * (n - 1) / 2





/-! ## 2-jets of power series -/

/-- `Jet f c₁ c₂` records that `f = 1 + c₁ X + c₂ X² + O(X³)`. -/
def Jet (f : PowerSeries ℤ) (c1 c2 : ℤ) : Prop :=
  constantCoeff f = 1 ∧ coeff 1 f = c1 ∧ coeff 2 f = c2












/-! ## The basic units `1 - X^m` -/

lemma isUnit_one_sub_X_pow {m : ℕ} (hm : 1 ≤ m) : IsUnit (1 - X ^ m : PowerSeries ℤ) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  have : (constantCoeff (X ^ m : PowerSeries ℤ)) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_X_pow]
    simp; omega
  simp [this]

/-- The unit `1 - X^m` of `ℤ⟦X⟧` (for `m = 0` we set it to `1`, a harmless default). -/
noncomputable def oneSubXPow (m : ℕ) : (PowerSeries ℤ)ˣ :=
  if h : 1 ≤ m then (isUnit_one_sub_X_pow h).unit else 1






/-! ## Divisor sums and the eta quotient product -/

/-- `bCoeff a m = ∑_{k ∣ m} a k`, the exponent of `(1 - q^m)` in the eta quotient. -/
def bCoeff (a : ℕ → ℤ) (m : ℕ) : ℤ := ∑ k ∈ m.divisors, a k



/-- The truncated normalised eta quotient `∏_{m=1}^{N} (1 - X^m)^{-b m}`,
as a unit of `ℤ⟦X⟧`.  This is the `q`-expansion of `q · η_a⁻¹` up to degree `N`. -/
noncomputable def etaQuotientProd (a : ℕ → ℤ) (N : ℕ) : (PowerSeries ℤ)ˣ :=
  ∏ m ∈ Icc 1 N, (oneSubXPow m) ^ (-(bCoeff a m))

/-- The head coefficient `c(1) = a₁(a₁+3)/2 + a₂`. -/
def headCoeff (a : ℕ → ℤ) : ℤ := a 1 * (a 1 + 3) / 2 + a 2







end EtaHead


