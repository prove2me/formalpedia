-- Prove2me | Theorems.Thm_mme_finset_prune_two_mode_collisions
-- name    : mme_finset_prune_two_mode_collisions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T19:49:55.702483+00:00
-- url     : https://prove2.me/theorems/f04bce32-d98f-4891-8005-d02e6ece1869
-- title:
--   Two-mode collision pruning loses at most the ordered conflict count
-- statement:
--   Let $E$ be a finite family whose elements carry two labels $x(e)$ and $y(e)$. There is a subfamily $F\subseteq E$ on which both label maps are injective and such that
--
--   $$
--   |E|\le |F|+\bigl|\{(e,e')\in E^2:e\ne e',\ x(e)=x(e')\text{ or }y(e)=y(e')\}\bigr|.
--   $$
--
--   Thus deleting all elements which participate in an $x$- or $y$-collision costs no more than the number of ordered collision pairs. This is the deterministic pruning estimate used after the first CW hash; it is independent of how the finite family and labels were produced.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 260–261: duplicate-block elimination and the observation that the number of eliminated triples is bounded by the number of shared-block pairs; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Prod

theorem mme_finset_prune_two_mode_collisions
    {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (E : Finset α) (x : α → β) (y : α → γ) :
    ∃ F : Finset α,
      F ⊆ E ∧
      Set.InjOn x (F : Set α) ∧
      Set.InjOn y (F : Set α) ∧
      E.card ≤ F.card +
        ((E.product E).filter (fun p =>
          p.1 ≠ p.2 ∧ (x p.1 = x p.2 ∨ y p.1 = y p.2))).card := by sorry
