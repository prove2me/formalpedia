-- Prove2me | Theorems.Thm_mme_finset_degree_threshold
-- name    : mme_finset_degree_threshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T20:26:00.206586+00:00
-- url     : https://prove2.me/theorems/04fb9e03-25b4-4c13-b2dc-accd2dcbf552
-- title:
--   Finite degree-threshold extraction with a mass bound
-- statement:
--   Let a finite set $E$ be labeled by $z:E\to\mathcal Z$, and assume every label fiber has size at most $D$. Keep exactly the fibers whose size is at least a threshold $H$, obtaining $F\subseteq E$. Then every represented fiber of $F$ still has at least $H$ elements, and\n\n$$\n|E|\le H\,|z(E)|+D\,|z(F)|.\n$$\n\nThis deterministic threshold lemma is the finite degree-averaging step used after collision pruning in the Coppersmith--Winograd hash. A lower bound on the surviving edge mass forces many Z-labels to remain while simultaneously giving every retained label a common positive degree lower bound.
-- source:
--   Elementary finite fiber counting; degree-threshold step used in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), common-degree C-tensor extraction on journal p. 271; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

theorem mme_finset_degree_threshold
    {α ζ : Type} [DecidableEq α] [DecidableEq ζ]
    (E : Finset α) (z : α → ζ) (H D : ℕ)
    (hmax : ∀ c ∈ E.image z,
      (E.filter (fun e => z e = c)).card ≤ D) :
    let F := E.filter (fun e =>
      H ≤ (E.filter (fun e' => z e' = z e)).card)
    F ⊆ E ∧
      (∀ c ∈ F.image z,
        H ≤ (F.filter (fun e => z e = c)).card) ∧
      E.card ≤ H * (E.image z).card + D * (F.image z).card := by sorry
