-- Prove2me | Theorems.Thm_take_append_self
-- name    : take_append_self
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-22T01:29:11.467166+00:00
-- url     : https://prove2.me/theorems/b6d97465-ddae-4226-91ef-3a4411a76163
-- title:
--   Taking prefix of concatenated lists returns the first list
-- statement:
--   Taking the first n elements from the concatenation of two lists, where n is the length of the first list, returns exactly the first list.

theorem take_append_self {α : Type} (l1 l2 : List α) :
    (l1 ++ l2).take l1.length = l1 := by sorry
