-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter20_endpoints_mem_of_mem_consecutiveEdges_local
-- name    : ProofsInTheBook.Chapter20.endpoints_mem_of_mem_consecutiveEdges_local
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:46:14.523825+00:00
-- url     : https://prove2.me/theorems/8a93e9ef-c5e4-4adf-9887-850b948d6f82
-- title:
--   Endpoints of a consecutive unordered edge belong to the list
-- statement:
--   For any type A, any list l of elements of A, and any $a,b\in A$, if the unordered pair $\{a,b\}$ occurs in the list of consecutive edges of l, then a and b both occur in l. No decidable-equality, distinctness, no-repetition, geometry, or dissection assumption is required. The unordered pair may have equal entries.
-- source:
--   Original declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter20E2Boundary.lean#L242. Repository topic: Monsky’s theorem, “One square and an odd number of triangles.”

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter20
set_option autoImplicit true
open ProofsInTheBook.Chapter20
open MonskyColor
variable (D : SquareDissection)

lemma ProofsInTheBook.Chapter20.endpoints_mem_of_mem_consecutiveEdges_local {α : Type*} {l : List α} {a b : α}
    (h : s(a, b) ∈ consecutiveEdges l) : a ∈ l ∧ b ∈ l := by sorry
