-- Prove2me | Theorems.Thm_KitchenQuery_parityOnSet_update_mem
-- name    : KitchenQuery.parityOnSet_update_mem
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:04:15.570246+00:00
-- url     : https://prove2.me/theorems/38cf5167-8e05-4100-bfac-93b767a518b7
-- title:
--   ParityOnSet update mem
-- statement:
--   Formal statement of `KitchenQuery.parityOnSet_update_mem` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem KitchenQuery.parityOnSet_update_mem{S : Finset (Fin n)} (x : Pantry n) {i : Fin n} (hi : i ∈ S) :
--       parityOnSet S (Function.update x i (!x i)) ≠ parityOnSet S x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/KitchenMenuSpectrum.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/KitchenMenuSpectrum.lean#L41

-- Thm stub generated from Novelty/KitchenMenuSpectrum.lean
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

theorem KitchenQuery.parityOnSet_update_mem{S : Finset (Fin n)} (x : Pantry n) {i : Fin n} (hi : i ∈ S) :
    parityOnSet S (Function.update x i (!x i)) ≠ parityOnSet S x := by sorry
