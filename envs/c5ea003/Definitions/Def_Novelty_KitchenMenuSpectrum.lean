-- Prove2me | Definitions.Def_Novelty_KitchenMenuSpectrum
-- name    : Novelty_KitchenMenuSpectrum
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:30:47.74425+00:00
-- url     : https://prove2.me/theorems/18793e38-ffb5-4480-a3fe-f844ec319eca
-- title:
--   Aether Catalog definitions — Novelty_KitchenMenuSpectrum
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.KitchenMenuSpectrum`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/KitchenMenuSpectrum.lean by skeleton subtraction
import Mathlib
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

namespace KitchenQuery

open Finset

variable {n : ℕ}

/-! ### Parity dishes supported on a set of ingredients -/

/-- The dish whose quality is the parity of the ingredients in `S`. -/
def parityOnSet (S : Finset (Fin n)) : Dish n :=
  fun x => decide (Odd (∑ j ∈ S, if x j then 1 else 0))




/-! ### Dishes that only use the first `k` ingredients -/

/-- `f` only uses the first `k` ingredients. -/
def UsesFirst (k : ℕ) (f : Dish n) : Prop :=
  ∀ x y : Pantry n, (∀ j : Fin n, (j : ℕ) < k → x j = y j) → f x = f y


/-- The parity dish on the first `k` ingredients: the mission's tunable recipe family. -/
def parityOn (k : ℕ) : Dish n := parityOnSet (Finset.univ.filter (fun j : Fin n => (j : ℕ) < k))




/-! ### The bridge to the barycentric menu calculus -/

/-- The timing record of a dish: cooking time `n`, verification time `tasteCost`. -/
noncomputable def toRecipe (f : Dish n) : RecipeBarycenter.Recipe :=
  ⟨cookCost f, tasteCost f⟩







/-! ### The mission's test: a census of one hundred recipes -/

/-- The census menu: on a pantry of `100` ingredients, the hundred dishes
`parityOn 1, …, parityOn 100`. -/
noncomputable def census100 (k : Fin 100) : RecipeBarycenter.Recipe :=
  toRecipe (parityOn (n := 100) ((k : ℕ) + 1))






/-! ### Quick recipes are rare -/




    

end KitchenQuery


