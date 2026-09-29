-- Prove2me | Theorems.Thm_diophantine_quintuple_not_b_le_3a_of_2a_le
-- name    : diophantine_quintuple_not_b_le_3a_of_2a_le
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-07T10:48:21.379606+00:00
-- url     : https://prove2.me/theorems/4e990b8a-b6cf-4321-a307-169f8149c0db
-- title:
--   No ordered Diophantine quintuple has 2a at most b at most 3a
-- statement:
--   Let $a<b<c<d<e$ be a Diophantine quintuple. Then the ratio regime $$2a\le b\le 3a$$ is impossible. This is Case 2 of Cipu and Fujita's proof that every ordered Diophantine quintuple satisfies $b>3a$; together with the complementary small-ratio case it exhausts $b\le3a$. Formalization note: $a=f_0$ and $b=f_1$ for an ordered quintuple $f$.
-- source:
--   Cipu and Fujita, Bounds for Diophantine quintuples, Glasnik Matematicki 50(1) (2015), Theorem 1.1, Case 2, https://doi.org/10.3336/gm.50.1.03

import Definitions.Def_diophantine_descent
set_option autoImplicit false
open DiophantineDescent

theorem diophantine_quintuple_not_b_le_3a_of_2a_le (f : Fin 5 → Nat)
    (hq : Quintuple f) (ho : Ordered f)
    (h1 : 2 * f 0 ≤ f 1) (h2 : f 1 ≤ 3 * f 0) : False := by sorry
