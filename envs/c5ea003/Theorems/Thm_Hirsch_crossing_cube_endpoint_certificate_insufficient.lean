-- Prove2me | Theorems.Thm_Hirsch_crossing_cube_endpoint_certificate_insufficient
-- name    : Hirsch.crossing_cube_endpoint_certificate_insufficient
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-09T14:30:51.58343+00:00
-- url     : https://prove2.me/theorems/3672334a-7c8c-4a5d-b95d-8629418d3bba
-- title:
--   Crossing endpoint-only repair certificates fail on Boolean cubes
-- statement:
--   For every Boolean cube dimension d at least six there are two unit-cost repair regions and a four-checkpoint crossing sequence whose two repair intervals cover all three old step slots, but the opposite cube endpoints admit no padded route of length five. Thus chronological crossing plus endpoint-local repair certificates alone cannot imply the loose L plus sum-of-budgets repair bound.
-- source:
--   Verified Lean obstruction from jjoshua2/prove2me-work PR #41.

import Mathlib
import Definitions.Def_Hirsch_model

open Set

namespace Hirsch

theorem crossing_cube_endpoint_certificate_insufficient (d : ℕ) (hd : 6 ≤ d) :
    let R : Finset (Fin d) → Finset (Fin d) → Prop := fun x y =>
      ∃ k, (k ∉ x ∧ y = insert k x) ∨ (k ∉ y ∧ x = insert k y)
    ∃ (w : ℕ → Finset (Fin d)) (S : Bool → Set (Finset (Fin d))),
      (∀ b, ∀ x ∈ S b, ∀ y ∈ S b,
        ∃ q : ℕ → Finset (Fin d), q 0 = x ∧ q 1 = y ∧
          ∀ j < 1, q j = q (j + 1) ∨ R (q j) (q (j + 1))) ∧
      w 0 ∈ S false ∧ w 2 ∈ S false ∧
      w 1 ∈ S true ∧ w 3 ∈ S true ∧
      (∀ j < 3, (0 ≤ j ∧ j < 2) ∨ (1 ≤ j ∧ j < 3)) ∧
      ¬ (∃ q : ℕ → Finset (Fin d), q 0 = w 0 ∧ q 5 = w 3 ∧
          ∀ j < 5, q j = q (j + 1) ∨ R (q j) (q (j + 1))) := by sorry

end Hirsch
