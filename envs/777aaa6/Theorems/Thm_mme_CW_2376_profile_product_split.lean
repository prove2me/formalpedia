-- Prove2me | Theorems.Thm_mme_CW_2376_profile_product_split
-- name    : mme_CW_2376_profile_product_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T17:49:53.308149+00:00
-- url     : https://prove2.me/theorems/9bb915e9-c86f-4181-8f3b-33c4ff6e9281
-- title:
--   Four-orbit product decomposition of the exact CW profile
-- statement:
--   Let $Q_\sigma$ be elements of any commutative monoid, indexed by the $125$ possible five-grade triples. Weight each element by the exact CW profile multiplicity. Then the full product splits into the four supported cyclic-orbit groups:
--
--   $$
--   \prod_\sigma Q_\sigma^{\mu_m(\sigma)}=\left(\prod_{\sigma\in\mathcal S}Q_\sigma\right)^{699m}\left(\prod_{\sigma\in\mathcal R}Q_\sigma\right)^{37{,}518m}\left(\prod_{\sigma\in\mathcal C}Q_\sigma\right)^{307{,}638m}\left(\prod_{\sigma\in\mathcal D}Q_\sigma\right)^{616{,}627m}.
--   $$
--
--   Unsupported types have multiplicity zero and disappear. This algebraic identity is independent of tensor semantics and can be reused to reduce the 125-type product to the fifteen supported constituents.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), the four orbit classes and exact multiplicities in equation (13), journal pp. 265--269; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_2376_address_block
open MME BigOperators

theorem mme_CW_2376_profile_product_split
    {M : Type} [CommMonoid M]
    (Q : (Fin 3 → Fin 5) → M) (m : ℕ) :
    (∏ σ, Q σ ^ cw2376ProfileMultiplicity m σ) =
      (∏ σ ∈ cw2376ScalarTypes, Q σ) ^ (699 * m) *
      (∏ σ ∈ cw2376RectTypes, Q σ) ^ (37518 * m) *
      (∏ σ ∈ cw2376CentralTypes, Q σ) ^ (307638 * m) *
      (∏ σ ∈ cw2376CoupledTypes, Q σ) ^ (616627 * m) := by
  sorry
