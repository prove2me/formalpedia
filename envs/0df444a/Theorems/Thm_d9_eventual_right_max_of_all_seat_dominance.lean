-- Prove2me | Theorems.Thm_d9_eventual_right_max_of_all_seat_dominance
-- name    : d9_eventual_right_max_of_all_seat_dominance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T10:42:59.203765+00:00
-- url     : https://prove2.me/theorems/9a888e53-2e41-4fab-ae5b-798edc9a4f30
-- title:
--   Right-sided eventual maximum from all-seat dominance
-- statement:
--   All-seat dominance implies a local maximum when one protection coordinate is varied to the right.
-- source:
--   Cause-linked repair of failed extracted publication f6b3517a-62ab-4b0a-8d03-e145646ec6d1; exact source declaration 120, with MeasureTheory scope and Topology filter notation restored in its preamble.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory
open NestedSeatAlloc.IntPolicy
open scoped Topology

theorem d9_eventual_right_max_of_all_seat_dominance
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (j n : ℕ) (s : ℝ) (hpj : 0 ≤ p j) (hs : 0 ≤ s)
    (hprev : ∀ t, 0 ≤ t → ∀ q, IsProtectionPolicy q →
      expRevenue P X f q n t ≤ expRevenue P X f p n t)
    (hupdate : ∀ u, 0 ≤ u → IsProtectionPolicy (Function.update p j u)) :
    ∀ᶠ u in 𝓝[Set.Ici (p j) \ {p j}] (p j),
      expRevenue P X f (Function.update p j u) n s ≤
        expRevenue P X f p n s := by sorry
