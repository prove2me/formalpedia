-- Prove2me | Theorems.Thm_d9Revenue_eq_of_policy_agree_below
-- name    : d9Revenue_eq_of_policy_agree_below
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T08:07:53.43011+00:00
-- url     : https://prove2.me/theorems/72e7b6c4-9875-47d7-8043-4db50a681701
-- title:
--   d9Revenue_eq_of_policy_agree_below
-- statement:
--   Automatically extracted helper theorem d9Revenue_eq_of_policy_agree_below from oversized parent candidate 029f41399a9b5b2cc3817d3867fba60227809162ca9c89b493c85daffb84e989.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:029f41399a9b5b2cc3817d3867fba60227809162ca9c89b493c85daffb84e989

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open NestedSeatAlloc.IntPolicy

theorem d9Revenue_eq_of_policy_agree_below
    (f p q x : ℕ → ℝ) :
    ∀ k, (∀ i, 1 ≤ i → i < k → p i = q i) →
      ∀ s, revenue f p x k s = revenue f q x k s := by sorry
