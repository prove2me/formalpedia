-- Prove2me | Theorems.Thm_diophantine_triple_non_euler_lower_bound
-- name    : diophantine_triple_non_euler_lower_bound
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-07T06:42:57.640468+00:00
-- url     : https://prove2.me/theorems/54dfe43a-91ce-4dd4-af67-06cc94b8ae10
-- title:
--   Gap bound for non-Euler triples (Jones lemma)
-- statement:
--   Let $a<b<c$ be a Diophantine triple that is not an Euler triple. Then $$c > 4ab.$$ This is the non-Euler case of the gap lemma for Diophantine triples: an Euler triple has the form $c = a+b+2r$ with $r^2 = ab+1$, while every other triple jumps past $4ab$. It supplies the outer lower bound of the five-interval split in the proof that no triple of degree at least two extends to a quintuple. Formalization note: triples, Euler triples, and degree are the project's `Triple`, `Euler`, and `HasDegree` predicates; degree at least two implies the non-Euler hypothesis, which is established separately, so this target isolates exactly the number-theoretic gap step.
-- source:
--   Bo He, Alain Togbe, Volker Ziegler, There is no Diophantine quintuple, arXiv:1610.04020v2, https://arxiv.org/abs/1610.04020v2; Lemma lem:Jones (preliminaries, restatement of Lemma 4 of Jones 1978: a triple with a<b<c satisfies c = a+b+2r or c > 4ab), applied in the proof of Theorem 9 (thm:deg2): since deg(a,b,c) >= 2 the triple is not Euler, hence c > 4ab. The remark after the lemma notes Jones' original statement differs slightly (c > 4c'ab with c' = 0 iff c = a+b+-2r).

import Definitions.Def_diophantine_descent
set_option autoImplicit false
open DiophantineDescent

theorem diophantine_triple_non_euler_lower_bound (a b c : Nat)
    (ht : Triple a b c) (hne : ¬ Euler a b c) : 4 * a * b < c := by sorry
