-- Prove2me | Theorems.Thm_mme_dwz_target_two_mode_collision_card_le_of_degree
-- name    : mme_dwz_target_two_mode_collision_card_le_of_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T22:00:58.258484+00:00
-- url     : https://prove2.me/theorems/237e6849-b544-4ad1-8f2d-b06f0a94e183
-- title:
--   Target-relative two-mode collision pairs are bounded by twice the degree
-- statement:
--   Let T be a target family inside an ambient family A, and let x and y be two labels. If every target element has at most d ambient elements sharing its x-label and at most d sharing its y-label, then the number of directed nontrivial pairs (a,b) in T×A sharing either label is at most 2|T|d. The target-relative orientation is what preserves the exact-profile scale in asymmetric hashing.
-- source:
--   Duan--Wu--Zhou asymmetric first-hash collision counting; finite target-relative degree bound.

import Mathlib

set_option autoImplicit false

/-!
# Target-relative two-mode collision count

This is the deterministic counting step in the asymmetric hash.  The first
edge of a directed collision is required to lie in the chosen joint-profile
family `T`, while the second may be any edge in the full marginal family
`A`.  Thus the bound scales with `T.card`, not `A.card`.
-/

theorem mme_dwz_target_two_mode_collision_card_le_of_degree
    {Edge X Y : Type}
    [DecidableEq Edge] [DecidableEq X] [DecidableEq Y]
    (A T : Finset Edge) (x : Edge → X) (y : Edge → Y) (d : ℕ)
    (hx : ∀ a ∈ T, (A.filter (fun b ↦ x b = x a)).card ≤ d)
    (hy : ∀ a ∈ T, (A.filter (fun b ↦ y b = y a)).card ≤ d) :
    ((T.product A).filter (fun p ↦
      p.1 ≠ p.2 ∧ (x p.1 = x p.2 ∨ y p.1 = y p.2))).card ≤
        2 * T.card * d := by
  sorry
