-- Prove2me | Theorems.Thm_diophantine_degree_ge_two_case_four_quintuple
-- name    : diophantine_degree_ge_two_case_four_quintuple
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-07T04:51:52.812296+00:00
-- url     : https://prove2.me/theorems/5d09b2c9-76ca-440d-bb22-ae6a9e44a70b
-- title:
--   Exclusion of degree at least two — Theorem 9, case IV
-- statement:
--   Let $a<b<c$ be an ordered Diophantine triple of degree at least two that extends to an ordered Diophantine quintuple $f$ with $f_0=a$, $f_1=b$, $f_2=c$. Assume the global bound $ac<6.77\cdot 10^{25}$ and the interval hypothesis $$4a^{3/2}b^{5/2}<c\le 4a^2b^3\quad\text{(squared lower bound }c^2>16a^3b^5\text{)}.$$ Then no such configuration exists. This is Case IV of the five-interval split in the proof of Theorem 9; it is eliminated by its own candidate-generation argument and finite computation. Formalization note: degree is the finite descent relation `HasDegree`, and the quintuple extension is witnessed by explicit `Quintuple` and `Ordered` hypotheses with `f 0 = a`, `f 1 = b`, `f 2 = c`.
-- source:
--   Bo He, Alain Togbé, Volker Ziegler, There is no Diophantine quintuple, arXiv:1610.04020v2, https://arxiv.org/abs/1610.04020v2; Section 9, proof of Theorem 9 (five-interval split).

import Definitions.Def_diophantine_descent
set_option autoImplicit false
open DiophantineDescent

theorem diophantine_degree_ge_two_case_four_quintuple (a b c n : Nat) (f : Fin 5 → Nat) (ht : Triple a b c)
    (hn : 2 ≤ n) (hd : HasDegree a b c n)
    (hq : Quintuple f) (ho : Ordered f) (ha : f 0 = a) (hb : f 1 = b) (hc : f 2 = c)
    (hglob : a * c < 67700000000000000000000000) (hlo : 16 * a ^ 3 * b ^ 5 < c ^ 2) (hhi : c ≤ 4 * a ^ 2 * b ^ 3) : False := by sorry
