-- Prove2me | Theorems.Thm_mme_CW_2376_profile_product_split_univ
-- name    : mme_CW_2376_profile_product_split_univ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T18:02:45.141077+00:00
-- url     : https://prove2.me/theorems/5f44b2ef-7eab-4aa0-b100-33a291573c6e
-- title:
--   Universe-polymorphic four-orbit decomposition of the exact CW profile
-- statement:
--   Let $Q_\sigma$ be elements of any commutative monoid, in an arbitrary type universe, indexed by the $125$ possible five-grade triples. The full multiplicity-weighted product splits into the scalar, rectangular, central, and coupled orbit products with exponents $699m$, $37{,}518m$, $307{,}638m$, and $616{,}627m$, respectively.
--
--   $$
--   \prod_\sigma Q_\sigma^{\mu_m(\sigma)}=\left(\prod_{\sigma\in\mathcal S}Q_\sigma\right)^{699m}\left(\prod_{\sigma\in\mathcal R}Q_\sigma\right)^{37{,}518m}\left(\prod_{\sigma\in\mathcal C}Q_\sigma\right)^{307{,}638m}\left(\prod_{\sigma\in\mathcal D}Q_\sigma\right)^{616{,}627m}.
--   $$
--
--   Unsupported types have multiplicity zero. Universe polymorphism allows this identity to be instantiated directly in the tensor-isomorphism quotient.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), the four orbit classes and exact multiplicities in equation (13), journal pp. 265--269; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_2376_address_block
open MME BigOperators
universe v

theorem mme_CW_2376_profile_product_split_univ
    {M : Type v} [CommMonoid M]
    (Q : (Fin 3 → Fin 5) → M) (m : ℕ) :
    (∏ σ, Q σ ^ cw2376ProfileMultiplicity m σ) =
      (∏ σ ∈ cw2376ScalarTypes, Q σ) ^ (699 * m) *
      (∏ σ ∈ cw2376RectTypes, Q σ) ^ (37518 * m) *
      (∏ σ ∈ cw2376CentralTypes, Q σ) ^ (307638 * m) *
      (∏ σ ∈ cw2376CoupledTypes, Q σ) ^ (616627 * m) := by
  sorry
