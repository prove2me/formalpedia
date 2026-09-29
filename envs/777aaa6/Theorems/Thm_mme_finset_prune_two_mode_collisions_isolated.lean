-- Prove2me | Theorems.Thm_mme_finset_prune_two_mode_collisions_isolated
-- name    : mme_finset_prune_two_mode_collisions_isolated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T19:59:30.59871+00:00
-- url     : https://prove2.me/theorems/cf346c9e-9697-46c7-aba7-4d1ea2b1342a
-- title:
--   Two-mode pruning leaves an isolated collision-free core
-- statement:
--   Let $E$ be a finite family with two labels $x(e)$ and $y(e)$. There is a subfamily $F\subseteq E$ which is isolated against the whole original family: for $e\in F$ and $e'\in E$, equality of either label forces $e=e'$. Moreover,
--
--   $$
--   |E|\le |F|+\bigl|\{(e,e')\in E^2:e\ne e',\ x(e)=x(e')\text{ or }y(e)=y(e')\}\bigr|.
--   $$
--
--   The isolation property is stronger than internal injectivity. In a CW hash bucket it ensures that a supported mixed edge using a retained X- or Y-block must be the intended retained edge, which is the finite inducedness condition needed after variable zeroing.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 260–261: eliminate blocks participating in duplicate triples and bound discarded triples by shared-block pairs; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Prod

theorem mme_finset_prune_two_mode_collisions_isolated
    {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (E : Finset α) (x : α → β) (y : α → γ) :
    ∃ F : Finset α,
      F ⊆ E ∧
      (∀ e ∈ F, ∀ e' ∈ E,
        x e = x e' ∨ y e = y e' → e = e') ∧
      E.card ≤ F.card +
        ((E.product E).filter (fun p =>
          p.1 ≠ p.2 ∧ (x p.1 = x p.2 ∨ y p.1 = y p.2))).card := by sorry
