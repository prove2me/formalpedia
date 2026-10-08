-- Prove2me | Theorems.Thm_d9_update_preserves_protection_policy
-- name    : d9_update_preserves_protection_policy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T08:07:33.249563+00:00
-- url     : https://prove2.me/theorems/50ab6c38-23eb-40de-af80-e702687163f6
-- title:
--   d9_update_preserves_protection_policy
-- statement:
--   Automatically extracted helper theorem d9_update_preserves_protection_policy from oversized parent candidate 029f41399a9b5b2cc3817d3867fba60227809162ca9c89b493c85daffb84e989.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:029f41399a9b5b2cc3817d3867fba60227809162ca9c89b493c85daffb84e989

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open NestedSeatAlloc.IntPolicy

theorem d9_update_preserves_protection_policy
    (p : ℕ → ℝ) (j : ℕ) (u : ℝ)
    (hp : IsProtectionPolicy p) (hu : 0 ≤ u) :
    IsProtectionPolicy (Function.update p j u) := by sorry
