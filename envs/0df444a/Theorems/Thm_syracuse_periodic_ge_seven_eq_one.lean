-- Prove2me | Theorems.Thm_syracuse_periodic_ge_seven_eq_one
-- name    : syracuse_periodic_ge_seven_eq_one
-- status  : Open
-- author  : @mysticflounder
-- created : 2026-09-09T00:40:06.163997+00:00
-- url     : https://prove2.me/theorems/e108a9c0-9ea8-4841-96f2-78bb716d0525
-- title:
--   No nontrivial Syracuse periodic point of iterate period at least seven
-- statement:
--   Let $T$ be the Syracuse map. The remaining high-period cycle assertion is
--
--   $$
--    m>0,\quad a\ge 7,\quad T^a(m)=m \Longrightarrow m=1.
--   $$
--
--   The cases $a=1,\ldots,6$ have separate proved formalizations. Thus this statement isolates precisely the unproved range needed to exclude all positive nontrivial Syracuse cycles. The integer $a$ is an iterate period, not necessarily the least period.
-- source:
--   Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), Section 8 (cycles), https://websites.umich.edu/~lagarias/3x%2B1.html; local formalization of the complementary periods through six: https://github.com/flound1129/collatz/tree/c0b24f073dcdc63d9d0974429bd8f3c522ed8eb4/lean/CollatzConjecture

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_periodic_ge_seven_eq_one (m period : ℕ)
    (hm : 0 < m) (hperiod : 7 ≤ period)
    (hcyc : syracuseStep^[period] m = m) :
    m = 1 := by
  sorry
