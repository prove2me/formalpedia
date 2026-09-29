-- Prove2me | solution 1 for KitchenQuery.card_filter_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:08:34.184934+00:00
-- url     : https://prove2.me/submissions/8986c367-f690-4eb6-bea1-2897f33c8092

-- Sol generated from Novelty/KitchenMenuSpectrum.lean
import Mathlib
import Definitions.Def_Novelty_KitchenMenuSpectrum
import Definitions.Def_Novelty_KitchenQueryComplexity
import Definitions.Def_Novelty_RecipeBarycenterBridge

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
theorem solution{k : ℕ} (hk : k ≤ n) :
    (Finset.univ.filter (fun j : Fin n => (j : ℕ) < k)).card = k := by
  classical
  have himg : (Finset.univ.filter (fun j : Fin n => (j : ℕ) < k))
      = Finset.image (fun i : Fin k => (⟨(i : ℕ), lt_of_lt_of_le i.isLt hk⟩ : Fin n))
        Finset.univ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hj
      exact ⟨⟨(j : ℕ), hj⟩, by ext; rfl⟩
    · rintro ⟨i, rfl⟩
      exact i.isLt
  rw [himg, Finset.card_image_of_injective _ ?_, Finset.card_univ, Fintype.card_fin]
  intro a b hab
  ext
  simpa using congrArg Fin.val hab
