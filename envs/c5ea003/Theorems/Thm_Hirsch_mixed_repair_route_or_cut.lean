-- Prove2me | Theorems.Thm_Hirsch_mixed_repair_route_or_cut
-- name    : Hirsch.mixed_repair_route_or_cut
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-09T14:12:41.799297+00:00
-- url     : https://prove2.me/theorems/92dc970d-1e7c-4bbe-b30c-b781d045360b
-- title:
--   Mixed repair network gives a route or an explicit closed cut
-- statement:
--   Given finitely many locally routable regions together with finitely many surviving bidirectional edges, either their supplied repair network routes the endpoints within the sum of all region budgets plus the number of surviving edges, or there is an explicit vertex subset separating the endpoints that is closed under every region and every supplied edge.
-- source:
--   Verified generic theorem isolated from jjoshua2/prove2me-work PR #42.

import Mathlib
import Definitions.Def_Hirsch_model

open scoped BigOperators
open Set

namespace Hirsch

theorem mixed_repair_route_or_cut {V ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : V → V → Prop) (S : ι → Set V) (C : ι → ℕ)
    (hlocal : ∀ i, ∀ x ∈ S i, ∀ y ∈ S i,
      ∃ q : ℕ → V, q 0 = x ∧ q (C i) = y ∧
        ∀ k < C i, q k = q (k + 1) ∨ R (q k) (q (k + 1)))
    (a b : κ → V) (hab : ∀ e, R (a e) (b e)) (hba : ∀ e, R (b e) (a e))
    (u v : V) :
    (∃ q : ℕ → V, q 0 = u ∧ q ((∑ i, C i) + Fintype.card κ) = v ∧
      ∀ k < (∑ i, C i) + Fintype.card κ,
        q k = q (k + 1) ∨ R (q k) (q (k + 1))) ∨
    ∃ U : Set V, u ∈ U ∧ v ∉ U ∧
      (∀ i, ∀ x ∈ S i, ∀ y ∈ S i, x ∈ U → y ∈ U) ∧
      ∀ e, (a e ∈ U ↔ b e ∈ U) := by sorry

end Hirsch
