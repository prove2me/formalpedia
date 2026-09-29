-- Prove2me | Theorems.Thm_diophantine_quintuple_degree_classification
-- name    : diophantine_quintuple_degree_classification
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-07T02:29:16.046979+00:00
-- url     : https://prove2.me/theorems/4da04ad5-a323-4124-a8c3-cd083a31b394
-- title:
--   Finite-degree classification of a putative quintuple
-- statement:
--   Let $f$ label five distinct positive integers having the Diophantine property. There is an increasing labelling $g$ of those same five integers whose first three entries have finite descent degree:
--   $$\exists n\in\mathbb N,\quad \deg(g_0,g_1,g_2)=n.$$
--
--   This is the existence part of the paper's classification, combined with increasing relabelling. It supplies the exhaustive degree cases needed for the headline theorem.
--
--   **Formalization Note** This specialization of Proposition 3 asserts existence only, not its quantitative bound or uniqueness. Degree is the finite descent relation; the matching condition and distinctness ensure that both labellings describe the same five-element set.
-- source:
--   Bo He, Alain Togbé, Volker Ziegler, There is no Diophantine quintuple, arXiv:1610.04020v2, https://arxiv.org/abs/1610.04020v2; Section 4, Proposition 3 (existence part), and Section 10 (increasing relabelling in the proof of Theorem 1).

import Definitions.Def_diophantine_descent
set_option autoImplicit false
open DiophantineDescent

theorem diophantine_quintuple_degree_classification (f : Fin 5 → Nat) (hq : Quintuple f) :
    ∃ g : Fin 5 → Nat, Quintuple g ∧ Ordered g ∧
      (∀ i, ∃ j, g i = f j) ∧ ∃ n : Nat, HasDegree (g 0) (g 1) (g 2) n := by sorry
