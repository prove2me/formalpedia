-- Prove2me | Theorems.Thm_mme_finite_injective_linear_code_first_second_moment
-- name    : mme_finite_injective_linear_code_first_second_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T22:28:41.193475+00:00
-- url     : https://prove2.me/theorems/388acb01-8b2a-4057-aa97-50a1e30165d1
-- title:
--   First and second moments for an injective family of finite linear hashes
-- statement:
--   Let $A$ be a finite injectively coded family of linear forms on $(\mathbb Z/M\mathbb Z)^{n+2}$. Assume every form has a unit coefficient and every pair whose codes are neither equal nor opposite has a unit $2\times2$ coefficient minor. If $D(w)$ counts the forms vanishing at $w$, then
--
--   $$
--   \sum_wD(w)=|A|M^{n+1},
--   $$
--
--   and
--
--   $$
--   \sum_wD(w)^2\le2|A|M^{n+1}+|A|^2M^n.
--   $$
--
--   The second term is the jointly uniform scale for nondependent pairs. Injectivity gives at most $2|A|$ equal-or-opposite ordered pairs, whose intersections are bounded at the one-equation scale. This is a cross-multiplied finite second-moment kernel tailored to affine-hash families with a unique complement dependency.
-- source:
--   Finite second-moment method with exact residue-ring linear fibers; the dependency pattern is the one used in Coppersmith--Winograd q=6 affine hashing on journal pp. 270--271

import Theorems.Thm_mme_ZMod_unit_linear_hash_fiber_card
import Theorems.Thm_mme_ZMod_two_linear_hash_fiber_card
import Theorems.Thm_mme_finset_equal_or_opposite_code_pairs_card_le
import Theorems.Thm_mme_finite_incidence_first_second_moment_identities

open BigOperators

set_option autoImplicit false

theorem mme_finite_injective_linear_code_first_second_moment
    {M n : ℕ} {α : Type} [NeZero M] [DecidableEq α]
    (A : Finset α)
    (c : α → Fin (n + 2) → ZMod M)
    (hunit : ∀ a ∈ A, ∃ j, IsUnit (c a j))
    (hinj : Function.Injective c)
    (hminor : ∀ a ∈ A, ∀ b ∈ A,
      c a ≠ c b → c a ≠ (fun i => -c b i) →
      ∃ j k, IsUnit (c a j * c b k - c a k * c b j)) :
    (∑ w : Fin (n + 2) → ZMod M,
        (A.filter (fun a => ∑ i, c a i * w i = 0)).card) =
          A.card * M ^ (n + 1) ∧
    (∑ w : Fin (n + 2) → ZMod M,
        (A.filter (fun a => ∑ i, c a i * w i = 0)).card ^ 2) ≤
          2 * A.card * M ^ (n + 1) + A.card ^ 2 * M ^ n := by
  sorry
