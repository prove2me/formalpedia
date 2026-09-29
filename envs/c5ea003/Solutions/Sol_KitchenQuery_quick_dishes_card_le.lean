-- Prove2me | solution 1 for KitchenQuery.quick_dishes_card_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:25:36.490451+00:00
-- url     : https://prove2.me/submissions/7c077326-01d3-47d7-9580-1efc22117135

-- Sol generated from Novelty/KitchenMenuSpectrum.lean
import Mathlib
import Definitions.Def_Novelty_KitchenMenuSpectrum
import Definitions.Def_Novelty_KitchenQueryComplexity
import Definitions.Def_Novelty_RecipeBarycenterBridge
import Theorems.Thm_KitchenQuery_quick_dish_classification

/-!
# The kitchen complexity spectrum: every ratio `C/V` occurs, and quick recipes are rare

This file continues `Novelty.KitchenQueryComplexity` and connects it to the convex-geometric
menu calculus of `Novelty.RecipeBarycenterBridge`.

Main contents.

* `parityOnSet`, `pivotalSet_parityOnSet`: the parity dish supported on a set `S` of
  ingredients is pivotal exactly on `S`.  Hence `tasteCost (parityOn k) = k` for every
  `k ≤ n` (`tasteCost_parityOn`): the whole spectrum of verification times is realised.
* `ratio_toRecipe_parityOn`: the cook/verify ratio of that dish is exactly `n / k`, so
  **every rational ratio `n/k` in `[1, n]` is realised by an actual dish**.
* `census100_*`: the mission's "classify 100 recipes" test, carried out formally: the
  hundred dishes `parityOn 1, …, parityOn 100` on a hundred ingredients have ratios
  `100/k`, and the aggregate menu ratio is exactly `200/101`.
* `ratio_eq_one_iff_evasive`, `menu_ratio_one_iff_all_evasive`: **the informal conjecture is
  inverted.**  `C(R) = V(R)` holds precisely for the *evasive* dishes — the hardest ones,
  such as the soufflé — while the *easy* dishes (salads) have the extreme ratio `C/V = n`.
  Combining with the barycentric rigidity theorem of `RecipeBarycenterBridge`, a whole menu
  is break-even iff every single dish on it is evasive.
* `quick_dish_classification`, `quick_dishes_card_le`, `quick_dishes_rare`: dishes with
  `V ≤ 1` are exactly constants, single-ingredient salads and their negations; there are at
  most `2n + 2` of them out of `2 ^ 2 ^ n` dishes, so quick recipes are vanishingly rare.
-/

open KitchenQuery

open Finset

variable {n : ℕ}

/-! ### Parity dishes supported on a set of ingredients -/





/-! ### Dishes that only use the first `k` ingredients -/







/-! ### The bridge to the barycentric menu calculus -/








/-! ### The mission's test: a census of one hundred recipes -/







/-! ### Quick recipes are rare -/




    


open KitchenQuery in
open scoped Classical in
theorem solution:
    (Finset.univ.filter (fun f : Dish n => tasteCost f ≤ 1)).card ≤ 2 * n + 2 := by
  classical
  set g : Bool ⊕ (Fin n × Bool) → Dish n := fun p => match p with
    | .inl b => fun _ => b
    | .inr (i, c) => fun x => xor c (x i) with hg
  have hsub : (Finset.univ.filter (fun f : Dish n => tasteCost f ≤ 1))
      ⊆ Finset.image g Finset.univ := by
    intro f hf
    have h := quick_dish_classification f (by simpa using (Finset.mem_filter.mp hf).2)
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    rcases h with ⟨b, hb⟩ | ⟨i, hi | hi⟩
    · exact ⟨.inl b, funext fun x => (hb x).symm⟩
    · exact ⟨.inr (i, false), funext fun x => by simp [hg, hi x]⟩
    · exact ⟨.inr (i, true), funext fun x => by simp [hg, hi x]⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_image_le) ?_
  simp [Finset.card_univ, Nat.mul_comm, Nat.add_comm]
