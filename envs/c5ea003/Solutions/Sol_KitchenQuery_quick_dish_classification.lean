-- Prove2me | solution 1 for KitchenQuery.quick_dish_classification
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:18:23.001074+00:00
-- url     : https://prove2.me/submissions/68cf8b00-59d5-4f2d-8884-21c2f731ad52

-- Sol generated from Novelty/KitchenMenuSpectrum.lean
import Mathlib
import Definitions.Def_Novelty_KitchenMenuSpectrum
import Definitions.Def_Novelty_KitchenQueryComplexity
import Definitions.Def_Novelty_RecipeBarycenterBridge
import Theorems.Thm_KitchenQuery_exists_optimal_taste

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

lemma depth_eq_zero_iff (t : Taste n) : t.depth = 0 ↔ ∃ b, t = .serve b := by
  cases t with
  | serve b => exact ⟨fun _ => ⟨b, rfl⟩, fun _ => rfl⟩
  | probe i l r =>
      constructor
      · intro h; simp [Taste.depth] at h
      · rintro ⟨b, hb⟩; exact absurd hb (by simp)



    


open KitchenQuery in
theorem solution(f : Dish n) (h : tasteCost f ≤ 1) :
    (∃ b, ∀ x, f x = b) ∨ ∃ i : Fin n, (∀ x, f x = x i) ∨ (∀ x, f x = !x i) := by
  obtain ⟨t, ht, hd⟩ := exists_optimal_taste f
  have hd1 : t.depth ≤ 1 := le_trans hd h
  cases t with
  | serve b => exact Or.inl ⟨b, fun x => (ht x).symm⟩
  | probe i l r =>
      have hl : l.depth = 0 := by simp only [Taste.depth] at hd1; omega
      have hr : r.depth = 0 := by simp only [Taste.depth] at hd1; omega
      obtain ⟨a, rfl⟩ := (depth_eq_zero_iff l).1 hl
      obtain ⟨c, rfl⟩ := (depth_eq_zero_iff r).1 hr
      have hf : ∀ x, f x = if x i then c else a := fun x => by
        rw [← ht x]; rfl
      cases a <;> cases c
      · exact Or.inl ⟨false, fun x => by rw [hf x]; cases x i <;> simp⟩
      · exact Or.inr ⟨i, Or.inl fun x => by rw [hf x]; cases x i <;> simp⟩
      · exact Or.inr ⟨i, Or.inr fun x => by rw [hf x]; cases x i <;> simp⟩
      · exact Or.inl ⟨true, fun x => by rw [hf x]; cases x i <;> simp⟩
