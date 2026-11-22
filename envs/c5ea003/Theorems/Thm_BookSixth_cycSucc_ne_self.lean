-- Prove2me | Theorems.Thm_BookSixth_cycSucc_ne_self
-- name    : BookSixth.cycSucc_ne_self
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-16T16:34:43.979197+00:00
-- url     : https://prove2.me/theorems/78c3f519-9ec2-4792-83dc-791dd9567022
-- title:
--   Cyclic successor is fixed-point-free
-- statement:
--   Cyclic successor on a finite set with at least two elements has no fixed point. For $l \ge 2$, the wraparound map $i \mapsto (i+1) \bmod l$ never fixes a point: a fixed point would force $(v+1) \bmod l = v$, impossible for $0 \le v < l$ with $l \ge 2$. This supplies the distinctness needed to read cycles as edge sets in the random graph model. **Formalization Note** Lean states it for the explicit `cycSucc` wraparound function.
-- source:
--   Fixed-point-freeness of cyclic successor, used in the high-girth high-chromatic-number argument, Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 45, https://doi.org/10.1007/978-3-662-57265-8_45

import Definitions.Def_BookSixthRandomGraph

set_option autoImplicit false

theorem BookSixth.cycSucc_ne_self (l : Nat) (hl0 : 0 < l) (hl1 : 1 < l) :
    forall i : Fin l, Ne (BookSixth.cycSucc hl0 i) i := by sorry
