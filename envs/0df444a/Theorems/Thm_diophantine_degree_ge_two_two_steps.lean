-- Prove2me | Theorems.Thm_diophantine_degree_ge_two_two_steps
-- name    : diophantine_degree_ge_two_two_steps
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-07T02:48:42.605574+00:00
-- url     : https://prove2.me/theorems/d6fb247d-3c2b-4597-8048-9a637f0daf20
-- title:
--   Degree at least two supplies two descent steps
-- statement:
--   If $\deg(a,b,c)=n\ge 2$ then the descent chain begins with two valid steps: there are $d_{-1}=d_-(a,b,c)$ and $d_{-2}=d_-(a,b,d_{-1})$ with the required positivity, ordering, and square-root identities at each stage. Follows by inverting the inductive degree relation twice. This is the starting point of the proof of Theorem 9.
-- source:
--   Bo He, Alain Togbé, Volker Ziegler, There is no Diophantine quintuple, arXiv:1610.04020v2, https://arxiv.org/abs/1610.04020v2; Section 9, proof of Theorem 9 ($d_{-1}=d_-(a,b,c)$, $d_{-2}=d_-(a,b,d_{-1})$).

import Definitions.Def_diophantine_descent
set_option autoImplicit false
open DiophantineDescent

theorem diophantine_degree_ge_two_two_steps (a b c n : Nat) (hn : 2 ≤ n)
    (hd : HasDegree a b c n) :
    ∃ x y z x' y' z' : Nat, Step a b c x y z ∧ Step x y z x' y' z' := by sorry
