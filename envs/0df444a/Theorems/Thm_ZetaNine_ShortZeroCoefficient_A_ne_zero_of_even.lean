-- Prove2me | Theorems.Thm_ZetaNine_ShortZeroCoefficient_A_ne_zero_of_even
-- name    : ZetaNine.ShortZeroCoefficient.A_ne_zero_of_even
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T13:42:45.070781+00:00
-- url     : https://prove2.me/theorems/50a9559f-7576-411d-a592-fc2f2527b1cd
-- title:
--   The genuine short-zero highest coefficient never vanishes at even degree
-- statement:
--   For every even natural number $n$ and every natural number $m$, the exact finite coefficient
--
--   $$A_{n,m}=28\sum_{j=0}^{n}(-1)^{m+j}\binom{n}{j}^{3}\binom{j+m}{m}^{7}\binom{n-j+m}{m}^{7}$$
--
--   is nonzero. This includes degree zero and, in particular, closes the original C3 coefficient-nonvanishing claim for every even $n\ge2$ with $14m\le3n+1$. The only hypothesis is evenness of $n$; no real-root property, gamma expansion, positivity identity or coefficient lower bound is assumed. It does not assert $A_{n,m}\zeta(9)+B_{n,m}\ne0$.
-- source:
--   https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02; research/short-zero-coefficient-nonvanishing.md, section 1 (the exact A_(n,m) definition and equation (1)), section 6 (equation (3) and the terminating Dixon factorial formula), section 7 (the coefficient nonvanishing conclusion). Verified Lean source: missions/zeta9/formalization/ShortZeroCoefficient.lean, lines 946–950, SHA256 9bf18387c4a51dd6dca03ecf197fc1cd85337fabf5b1d3421e2302e452347dbc.

import Definitions.Def_ZetaNine_ShortZeroCoefficient
import Mathlib.Algebra.Group.Even
open scoped BigOperators
open ZetaNine.ShortZeroCoefficient

theorem ZetaNine.ShortZeroCoefficient.A_ne_zero_of_even (n m : ℕ) (hn : Even n) : A n m ≠ 0:= by sorry
