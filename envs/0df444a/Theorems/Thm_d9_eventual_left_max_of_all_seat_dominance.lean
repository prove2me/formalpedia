-- Prove2me | Theorems.Thm_d9_eventual_left_max_of_all_seat_dominance
-- name    : d9_eventual_left_max_of_all_seat_dominance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T10:42:21.216717+00:00
-- url     : https://prove2.me/theorems/e20afe79-4d8c-442d-b873-af6f211a14a2
-- title:
--   Left-sided eventual maximum from all-seat dominance
-- statement:
--   All-seat dominance implies a local maximum when one positive protection coordinate is varied to the left.
-- source:
--   Cause-linked repair of failed extracted publication 2752afff-be97-4018-b2da-0bfa06e209fa; exact source declaration 121, with MeasureTheory scope and Topology filter notation restored in its preamble.

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open MeasureTheory
open NestedSeatAlloc.IntPolicy
open scoped Topology

theorem d9_eventual_left_max_of_all_seat_dominance
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (j n : ℕ) (s : ℝ) (hpj : 0 < p j) (hs : 0 ≤ s)
    (hprev : ∀ t, 0 ≤ t → ∀ q, IsProtectionPolicy q →
      expRevenue P X f q n t ≤ expRevenue P X f p n t)
    (hupdate : ∀ u, 0 ≤ u → IsProtectionPolicy (Function.update p j u)) :
    ∀ᶠ u in 𝓝[Set.Iic (p j) \ {p j}] (p j),
      expRevenue P X f (Function.update p j u) n s ≤
        expRevenue P X f p n s := by sorry
