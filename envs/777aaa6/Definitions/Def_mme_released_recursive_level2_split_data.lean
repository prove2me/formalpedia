-- Prove2me | Definitions.Def_mme_released_recursive_level2_split_data
-- name    : mme_released_recursive_level2_split_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-22T22:02:11.478934+00:00
-- url     : https://prove2.me/theorems/5b17d80e-d6d1-4f7d-9eb0-6ee1a393acd6
-- title:
--   Level-two split data as explicit small integers
-- statement:
--   The level-two split data of the released recursive construction, as explicit small integers: a grade triple of a region, the split weight of a triple before the region's own scale, the parent mixture as a quotient over the scale, and the grade marginal of a region in one mode.
-- source:
--   Assembly of the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6) over the Duan-Wu-Zhou fourth-power construction (https://arxiv.org/html/2210.10173v5, section 7).

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters

open BigOperators MME MME.RecursiveYZ MME.RecStage
open scoped Classical
set_option autoImplicit false

namespace MME.L2Cert

/-- Grade triples of a level-two region. -/
abbrev Tri : Type := Fin 3 → Fin (2 * 2 ^ (1 - 1) + 1)

/-- The small split weight of a level-two region, before the region's own scale. -/
def jwv (r : Fin 1104) (a : Tri) : ℕ :=
  jw (parent2 r 0) (parent2 r 1) (parent2 r 2) (l2At r).2.2 (a 0).val (a 1).val (a 2).val

/-- The level-two parent mixture, as an explicit small-integer quotient. -/
def PL (i : Fin 3) (r : Fin 1104) (w : Fin 2 → CompleteSplit.CompleteWord 1) : ℚ :=
  (∑ a : Tri,
    if ((a 0).val + (a 1).val + (a 2).val = 2 * 2 ^ (1 - 1) ∧ ∀ k, (a k).val ≤ parent2 r k) ∧
        ((w 0 0).val = (a i).val ∧ (w 1 0).val = parent2 r i - (a i).val) then
      (jwv r a : ℚ) else 0) / (D : ℚ)

/-- The grade marginal of a level-two region in one mode, before the scale. -/
def Jm (r : Fin 1104) (i : Fin 3) (v : Fin 3) : ℕ :=
  ∑ x : Fin 3, ∑ y : Fin 3, ∑ z : Fin 3,
    if (((![x, y, z] : Tri) 0).val + (![x, y, z] : Tri) 1 + (![x, y, z] : Tri) 2 = 2 * 2 ^ (1 - 1) ∧
        ∀ k, ((![x, y, z] : Tri) k).val ≤ parent2 r k) ∧ v.val = ((![x, y, z] : Tri) i).val then
      jwv r ![x, y, z] else 0

end MME.L2Cert


