-- Prove2me | Theorems.Thm_Hirsch_q28_cardAt_eq_popcount_high
-- name    : Hirsch.q28_cardAt_eq_popcount_high
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-06T01:31:20.216319+00:00
-- url     : https://prove2.me/theorems/07156fd7-d89e-476a-aeca-2ede958c0e94
-- title:
--   Common-active cards of $Q_{28}$ orbits $10$--$19$ match popcount
-- statement:
--   The stored common-active cardinality of two $Q_{28}$ orbit labels agrees with the $28$-bit popcount of their tight-mask conjunction, for the last ten orbit indices.
--
--   Let $o_1,o_2$ range over the twenty stored nonnegative orbit labels of the polar of the prismatoid $Q_{28}$, and let $s$ range over the sixteen coordinatewise sign patterns. Write $N(o,s)$ for the integer whose bits record the active supporting rows of the signed representative of orbit $o$ with signs $s$, and write $c(o_1,o_2,s)$ for the stored number of common active rows of the unsigned representative of $o_1$ with the $s$-signed representative of $o_2$.
--
--   $$
--   c(o_1,o_2,s)=\operatorname{popcount}_{28}\bigl(N(o_1,0)\land N(o_2,s)\bigr)
--   \qquad\text{whenever }10\le o_1\le 19.
--   $$
--
--   This is the high-index half of the $20\times 20\times 16$ lookup that transfers adjacency of extreme points to the stored quotient.
--
--   Formalization Note. In Lean the bound is `10 \le o1.val` with `o1 : Fin 20`.
-- source:
--   Santos, A counterexample to the Hirsch conjecture, arXiv:1006.2814, §2.2; Matschke--Santos--Weibel, The width of 5-dimensional prismatoids, arXiv:1202.4701, Corollary 2.9

import Mathlib
import Definitions.Def_Hirsch_q28_cert

open Hirsch

namespace Hirsch

theorem q28_cardAt_eq_popcount_high :
    ∀ (o1 o2 : Fin 20) (s : Fin 16),
      10 ≤ o1.val →
        commonActiveCard o1 o2 s =
          popcount28 (Nat.land (tightMask o1 0) (tightMask o2 s)) := by sorry
end Hirsch
