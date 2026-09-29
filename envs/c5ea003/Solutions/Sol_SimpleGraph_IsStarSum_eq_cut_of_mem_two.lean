-- Prove2me | solution 1 for SimpleGraph.IsStarSum.eq_cut_of_mem_two
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T13:23:58.333149+00:00
-- url     : https://prove2.me/submissions/abcbd0fa-86a0-4b62-9a3e-778a185e4a9f

/-
# `SimpleGraph.IsStarSum.eq_cut_of_mem_two`
Target `b996f45a` (WA x5). Gift: SAFE.

BINDERS from this target's OWN WA, verbatim — note `h` is a LEADING POSITIONAL argument and
`{x i j}` are implicit, neither of which is visible in the published statement text:
    ∀ {V} {ι} {G : SimpleGraph V} {H : ι → SimpleGraph V} {A : ι → Set V} {v : V},
      G.IsStarSum H A v → ∀ {x : V} {i j : ι}, i ≠ j → x ∈ A i → x ∈ A j → x = v

MATHS. `IsStarSum` carries the field `inter_eq : ∀ i j, i ≠ j → A i ∩ A j = {v}`. A point in two
distinct sides is in their intersection, which is the singleton `{v}` — and for `Set`, membership
in `{v}` IS the equation `x = v`.
-/
import Mathlib
import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis
import Definitions.Def_Novelty_OneSumStarAmalgam

set_option maxHeartbeats 400000

open SimpleGraph Finset

open SimpleGraph in
/-- **The target, verbatim.** -/
theorem solution {V ι : Type*} {G : SimpleGraph V} {H : ι → SimpleGraph V} {A : ι → Set V} {v : V}
    (h : G.IsStarSum H A v) {x : V} {i j : ι} (hij : i ≠ j) (hi : x ∈ A i) (hj : x ∈ A j) :
    x = v := by
  have hx : x ∈ A i ∩ A j := ⟨hi, hj⟩
  rw [h.inter_eq i j hij] at hx
  exact hx
