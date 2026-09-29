-- Prove2me | Theorems.Thm_diophantine_descent_step_exists
-- name    : diophantine_descent_step_exists
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-07T04:02:59.953447+00:00
-- url     : https://prove2.me/theorems/f63c39bb-6593-4289-b407-eded17381398
-- title:
--   Descent step exists for non-Euler triples
-- statement:
--   Let $a<b<c$ be a non-Euler Diophantine triple. Then one descent step applies: with $r^2=ab+1$, $s^2=ac+1$, $t^2=bc+1$ and $m=a+b+c+2abc-2rst$, we have $0<m<c$ and the increasing rearrangement of $a,b,m$ is again a Diophantine triple. That is, the paper's $\partial_{-1}$-operator is well defined. This is the hard number-theoretic half of Proposition 3 (Lemma 7); termination is handled separately by induction on the largest entry.
-- source:
--   Bo He, Alain Togbé, Volker Ziegler, There is no Diophantine quintuple, arXiv:1610.04020v2, https://arxiv.org/abs/1610.04020v2; Sections 3-4, Lemma 7 (well-definedness of the descent operator).

import Definitions.Def_diophantine_descent
set_option autoImplicit false
open DiophantineDescent

theorem diophantine_descent_step_exists (a b c : Nat) (h : Triple a b c) (hne : ¬ Euler a b c) :
    ∃ x y z : Nat, Step a b c x y z := by sorry
