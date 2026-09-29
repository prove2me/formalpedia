-- Prove2me | Theorems.Thm_diophantine_triple_finite_degree
-- name    : diophantine_triple_finite_degree
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-07T02:46:42.939804+00:00
-- url     : https://prove2.me/theorems/20d2851c-b046-4967-93c1-35a95ce3004a
-- title:
--   Every Diophantine triple has finite descent degree
-- statement:
--   Every ordered Diophantine triple $a<b<c$ with $ab+1$, $ac+1$, $bc+1$ all squares reaches an Euler triple after finitely many descent steps: $$\exists n\in\mathbb{N},\quad \deg(a,b,c)=n.$$ This is the existence part of the classification (it supplies termination of the descent operator), separated from any quintuple context so it can be reused. It does not assert the quantitative bound or uniqueness.
-- source:
--   Bo He, Alain Togbé, Volker Ziegler, There is no Diophantine quintuple, arXiv:1610.04020v2, https://arxiv.org/abs/1610.04020v2; Section 4, Proposition 3 (existence part).

import Definitions.Def_diophantine_descent
set_option autoImplicit false
open DiophantineDescent

theorem diophantine_triple_finite_degree (a b c : Nat) (h : Triple a b c) :
    ∃ n : Nat, HasDegree a b c n := by sorry
