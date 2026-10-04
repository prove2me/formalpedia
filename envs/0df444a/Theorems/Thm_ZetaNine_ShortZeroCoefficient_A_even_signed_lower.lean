-- Prove2me | Theorems.Thm_ZetaNine_ShortZeroCoefficient_A_even_signed_lower
-- name    : ZetaNine.ShortZeroCoefficient.A_even_signed_lower
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-03T13:42:37.694028+00:00
-- url     : https://prove2.me/theorems/dbbbbec1-10e9-4f66-a0a7-b9f9cf1cdf48
-- title:
--   All-parameter signed lower bound for the genuine short-zero coefficient
-- statement:
--   For every pair of natural numbers $d,m$, the actual highest coefficient $A_{2d,m}$ of the original short-zero construction satisfies
--
--   $$(-1)^{m+d}A_{2d,m}\ge28\binom{2d}{d}\binom{3d}{d}\binom{d+m}{m}^{14}>0.$$
--
--   The theorem covers all even degrees $n=2d$, including $n=0$, and every $m\ge0$. In particular it applies to every even $n\ge2$ in the original analytic parameter domain $14m\le3n+1$. The product $\binom{2d}{d}\binom{3d}{d}$ is $(3d)!/(d!)^3$, so this is the fully explicit bound in section 6. No positivity, gamma expansion or nonvanishing assumption is imposed on the coefficient. This concerns the finite coefficient $A$, and does not assert nonvanishing or decay of $A\zeta(9)+B$.
-- source:
--   https://github.com/Anchen0823/zeta9-research-notes/releases/tag/research-2026-10-02; research/short-zero-coefficient-nonvanishing.md, section 1 (the exact A_(n,m) definition and equation (1)), section 6 (equation (3) and the terminating Dixon factorial formula), section 7 (the coefficient nonvanishing conclusion). Verified Lean source: missions/zeta9/formalization/ShortZeroCoefficient.lean, lines 919–923, SHA256 9bf18387c4a51dd6dca03ecf197fc1cd85337fabf5b1d3421e2302e452347dbc.

import Definitions.Def_ZetaNine_ShortZeroCoefficient
import Mathlib.Algebra.Group.Even
open scoped BigOperators
open ZetaNine.ShortZeroCoefficient

theorem ZetaNine.ShortZeroCoefficient.A_even_signed_lower (d m : ℕ) :
    (28 : ℤ) * ((2 * d).choose d : ℤ) * ((3 * d).choose d : ℤ) *
        ((d + m).choose m : ℤ) ^ 14 ≤ (-1 : ℤ) ^ (m + d) * A (2 * d) m:= by sorry
