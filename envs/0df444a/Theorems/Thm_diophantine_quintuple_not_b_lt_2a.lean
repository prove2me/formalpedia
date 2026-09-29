-- Prove2me | Theorems.Thm_diophantine_quintuple_not_b_lt_2a
-- name    : diophantine_quintuple_not_b_lt_2a
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-07T10:48:19.567301+00:00
-- url     : https://prove2.me/theorems/aacdd6f0-17e6-4304-a005-51cf0db786eb
-- title:
--   No ordered Diophantine quintuple has b below 2a
-- statement:
--   Let $a<b<c<d<e$ be a Diophantine quintuple. Then the ratio regime $$b<2a$$ is impossible. This is Case 1 of Cipu and Fujita's proof that every ordered Diophantine quintuple satisfies $b>3a$; it isolates the small-ratio branch used by later extension criteria. Formalization note: $a=f_0$ and $b=f_1$ for an ordered quintuple $f$.
-- source:
--   Cipu and Fujita, Bounds for Diophantine quintuples, Glasnik Matematicki 50(1) (2015), Theorem 1.1, Case 1, https://doi.org/10.3336/gm.50.1.03

import Definitions.Def_diophantine_descent
set_option autoImplicit false
open DiophantineDescent

theorem diophantine_quintuple_not_b_lt_2a (f : Fin 5 → Nat)
    (hq : Quintuple f) (ho : Ordered f) (hlt : f 1 < 2 * f 0) : False := by sorry
