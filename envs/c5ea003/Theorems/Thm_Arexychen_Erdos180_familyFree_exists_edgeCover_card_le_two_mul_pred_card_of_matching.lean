-- Prove2me | Theorems.Thm_Arexychen_Erdos180_familyFree_exists_edgeCover_card_le_two_mul_pred_card_of_matching
-- name    : Arexychen.Erdos180.familyFree_exists_edgeCover_card_le_two_mul_pred_card_of_matching
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-09T07:20:00.085097+00:00
-- url     : https://prove2.me/theorems/c57daeb7-95c2-4c82-88ca-2a5945cb8e79
-- title:
--   A forbidden matching member gives a bounded edge-covering vertex set
-- statement:
--   Let $F$ be a finite indexed family of finite simple graphs, and let $j$ be an index whose reduced graph is a matching with at least two edges. Every $F$-free graph $G$ on $\operatorname{Fin}(n)$ has a vertex set $T$ meeting every edge and satisfying
--
--   $$|T|\le 2\bigl(|V(F_j)|-1\bigr).$$
--
--   The bound uses the whole vertex set of $F_j$, including isolated vertices, and natural-number subtraction. An index $j$ is supplied; there is no separate nonempty-typeclass binder.
-- source:
--   https://github.com/arexychen/Erdos180/blob/2ea42256708d02f5de1541b42cfbc1e1c00c7d03/Erdos180/Families/Upper.lean#L169-L216

import Definitions.Def_arexychen_erdos180_families_bounds
import Definitions.Def_arexychen_erdos180_finite
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Tactic

open Filter
open Asymptotics
universe u v w
open Arexychen.Erdos180

theorem Arexychen.Erdos180.familyFree_exists_edgeCover_card_le_two_mul_pred_card_of_matching
    {ι : Type v} [Finite ι] {F : ι → FiniteSimpleGraph.{u}}
    {j : ι}
    (hmatching : (F j).matchingWithAtLeastTwoEdgesAfterDeletingIsolated)
    {n : ℕ} (G : SimpleGraph (Fin n))
    (hfree : FamilyFree F G) :
    ∃ T : Finset (Fin n),
      T.card ≤ 2 * (Fintype.card (F j).V - 1) ∧
        ∀ ⦃x y : Fin n⦄, G.Adj x y → x ∈ T ∨ y ∈ T := by sorry
