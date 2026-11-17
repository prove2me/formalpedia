-- Prove2me | Theorems.Thm_XiPairingPublished_paired_canonical_product
-- name    : XiPairingPublished.paired_canonical_product
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T10:29:32.164815+00:00
-- url     : https://prove2.me/theorems/5dabe6dd-27bd-45fc-bf2e-da61d14e0cf7
-- title:
--   Pairing opposite genus-one factors in convergent canonical products
-- statement:
--   For an arbitrary index I, complex numbers a_i and z, assume the two genus-one factor families E(z/a_i) and E(z/(-a_i)) are multipliable, where E(w)=(1-w)exp(w). Then the paired family 1+z²/(-a_i²) is multipliable, and its product is the product of the two original products. The proof cancels the exponential factors exactly and uses justified multiplication of convergent infinite products. This generic lemma does not assert that a_i enumerate the upper zeros of xi, or establish the needed reindexing by multiplicity. It is a component of the concrete xi product normalization, not a proof of RH.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandao Bueno. Continuation of ActualXiBranches and XiHadamardPort, 2026-11-16. https://app.notion.com/p/41a98395ac6e8160a225d82e667ec8e4. Elementary/classical identity, no novelty claim.

import Mathlib

theorem XiPairingPublished.paired_canonical_product {I : Type*} (a : I → ℂ) (z : ℂ)
    (hp : Multipliable (fun i => (1-z/a i)*Complex.exp (z/a i)))
    (hm : Multipliable (fun i => (1-z/(-a i))*Complex.exp (z/(-a i)))) :
    Multipliable (fun i => 1+z^2/(-(a i)^2)) ∧
    (∏' i, (1-z/a i)*Complex.exp (z/a i)) *
    (∏' i, (1-z/(-a i))*Complex.exp (z/(-a i))) =
      ∏' i, (1+z^2/(-(a i)^2)) := by sorry
