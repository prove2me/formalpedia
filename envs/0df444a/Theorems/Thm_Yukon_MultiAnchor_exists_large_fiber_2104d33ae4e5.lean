-- Prove2me | Theorems.Thm_Yukon_MultiAnchor_exists_large_fiber_2104d33ae4e5
-- name    : Yukon.MultiAnchor.exists_large_fiber_2104d33ae4e5
-- status  : Proved
-- author  : @yukon
-- created : 2026-09-29T21:58:24.756791+00:00
-- url     : https://prove2.me/theorems/6ef9e887-2f89-4d42-9a1f-779237652da3
-- title:
--   A large fiber exists when the domain outnumbers bounded fibers
-- statement:
--   For finite types α and β and a function f : α → β, if |β| · s < |α|, some fiber of f has more than s elements. This pigeonhole lemma is used in the multi-anchor attack construction. Original contributor: saucegodbased; verified Better Codes submission 1ef57658-6336-410f-add5-9247de860f71. Extracted from Lean 4.32.2 source; only the declaration name and import context were adapted for publication. The statement and proof body are unchanged.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/3868a58143da865af79e8d6451ba81de2edc140a/ProximityPrize/SubmissionUpper/MultiAnchorCombinatorics.lean#L200
--
--   history-3868a581-exists-large-fiber-v1
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJoaXN0b3J5LTM4NjhhNTgxLWV4aXN0cy1sYXJnZS1maWJlci12MSIsImhhc2giOiJiMTY4YjNkMjE3MzEzZDMyYWJlZjkyZDM3NjNkMzQ2OWVlMjkwZWMxM2IxMzQwMWQxNjU5YWJhNDRkN2QyYjQ0Iiwia2luZCI6InByb2JsZW0iLCJ0YXJnZXQiOiJZdWtvbi5NdWx0aUFuY2hvci5leGlzdHNfbGFyZ2VfZmliZXJfMjEwNGQzM2FlNGU1IiwiZW52aXJvbm1lbnQiOnsidG9vbGNoYWluIjoibGVhbnByb3Zlci9sZWFuNDp2NC4zMy4xIiwibWF0aGxpYlJldiI6IjBkZjQ0NGEzNjBlYWE2MGFiOGMxMWRjYTUxYTg2YWY2OTI5NTU0NzQifSwidGFnIjoiYmV0dGVyLWNvZGVzLWhpc3RvcnkifQ]

import Mathlib
open scoped BigOperators

theorem Yukon.MultiAnchor.exists_large_fiber_2104d33ae4e5 {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (sieve : Nat)
    (hlarge : Fintype.card β * sieve < Fintype.card α) :
    ∃ y : β, sieve < (Finset.univ.filter fun x : α => f x = y).card  := by sorry
