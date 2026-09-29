-- Prove2me | Theorems.Thm_mme_multipart_card_split
-- name    : mme_multipart_card_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-23T06:04:36.201259+00:00
-- url     : https://prove2.me/theorems/1d5c6b9f-2a7d-4951-a222-a7588b8f63c8
-- title:
--   Counting blocks with a property splits over the parts
-- statement:
--   Counting the blocks with a given property splits over the parts of any assignment.
--
--   When blocks are distributed among several parts, the number of blocks satisfying a property is the
--   sum, over the parts, of the number satisfying it within that part. This is what lets a condition
--   stated per part be reassembled into the same condition stated globally: each part certifies its own
--   share of a histogram, and the shares add up to the whole.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Mathlib

open BigOperators
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u

theorem mme_multipart_card_split :
    ∀ {B : Type u} [Fintype B] {p : ℕ} (part : B → Fin p) (P : B → Prop),
      Fintype.card {b : B // P b} = ∑ j, Fintype.card {b : B // part b = j ∧ P b} := by sorry
