-- Prove2me | Theorems.Thm_ZudilinZeta_zudilin_series_summable
-- name    : ZudilinZeta.zudilin_series_summable
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-22T18:08:02.77976+00:00
-- url     : https://prove2.me/theorems/55b395a9-53e2-42c0-9f60-3895aba3ec0f
-- title:
--   Convergence of the series defining $F_n$ (from $R_n(t) = O(t^{-2})$)
-- statement:
--   Zudilin's note remarks that condition (1) forces $R_n(t) = O(t^{-2})$, which is what guarantees that the series on the right-hand side of (2) converges.
--
--   Formally: for every admissible parameter set and every $n > 0$, the family $t \mapsto R_n^{(r-1)}(t)$, indexed by the natural numbers $t = 0, 1, 2, \dots$, is summable. Without this, the value $F_n$ defined by (2) would carry no meaning.
-- source:
--   W. V. Zudilin, One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Uspekhi Mat. Nauk 56:4 (2001), 149–150, https://doi.org/10.4213/rm427 (English transl.: Russian Math. Surveys 56:4 (2001), 774–776)

import Definitions.Def_ZudilinZetaSetup

namespace ZudilinZeta
theorem zudilin_series_summable (P : Params) (n : ℕ) (hn : 0 < n) :
    Summable (fun t : ℕ => iteratedDeriv (P.r - 1) (R P n) (t : ℝ)) := by sorry
end ZudilinZeta
