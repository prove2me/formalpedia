-- Prove2me | Theorems.Thm_mme_position_card_eq
-- name    : mme_position_card_eq
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-18T18:22:39.383187+00:00
-- url     : https://prove2.me/theorems/b8d9df84-9447-43ed-b893-c850565938fc
-- title:
--   Physical position census
-- statement:
--   Physical positions are one pair per parent occurrence.
--
--   The type $Position(n)$ consists of triples $(r,t,h)$ with $r$ a region, $t$ an occurrence, and $h$ a half, so its cardinality is twice the total occurrences $2\sum_r n_r$.
--
--   **Formalization Note** Direct cardinality computation; used to pin the $N=2$ skeleton.
-- source:
--   Cardinality of MME.RecursiveYZ.Position; skeleton lemma for the N=2 regional analysis.

import Definitions.Def_mme_recursive_yz_physical_words
open scoped BigOperators
set_option autoImplicit false

theorem mme_position_card_eq : forall (R : Nat) (n : Fin R → Nat), Fintype.card (MME.RecursiveYZ.Position n) = 2 * ∑ r, n r := by sorry
