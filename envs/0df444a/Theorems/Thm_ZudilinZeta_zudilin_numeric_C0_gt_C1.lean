-- Prove2me | Theorems.Thm_ZudilinZeta_zudilin_numeric_C0_gt_C1
-- name    : ZudilinZeta.zudilin_numeric_C0_gt_C1
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-22T19:53:03.453661+00:00
-- url     : https://prove2.me/theorems/14b927eb-b210-4e9f-8ca4-3258b8e4a059
-- title:
--   At $r=3$, $q=13$: $C_0 = 227.58019641\ldots > C_1 = 226.24944266\ldots$
-- statement:
--   The final paragraph of the note: for $r = 3$, $q = 13$ and
--   $$\eta_0 = 91,\quad \eta_1 = \eta_2 = \eta_3 = 27,\quad \eta_4 = 29,\ \eta_5 = 30,\ \eta_6 = 31,\ \dots,\ \eta_{12} = 37,\ \eta_{13} = 38,$$
--   one has $C_0 = 227.58019641\dots$ and $C_1 = 226.24944266\dots$, so $C_0 > C_1$ and, by Lemma 3, there is an irrational number among $\zeta(5), \zeta(7), \zeta(9), \zeta(11)$.
--
--   The decimal expansions given in the note are read here as: $227.58019641 \le C_0 < 227.58019642$ and $226.24944266 \le C_1 < 226.24944267$; the inequality $C_1 < C_0$ is stated separately so that a solver may establish it by any means, for instance by cruder rigorous bounds.
-- source:
--   W. V. Zudilin, One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Uspekhi Mat. Nauk 56:4 (2001), 149–150, https://doi.org/10.4213/rm427 (English transl.: Russian Math. Surveys 56:4 (2001), 774–776)

import Definitions.Def_ZudilinZetaAsymp
import Definitions.Def_ZudilinZetaParams13

namespace ZudilinZeta
theorem zudilin_numeric_C0_gt_C1 (τ₀ : ℂ)
    (hroot : charPoly params13 τ₀ = 0) (him : 0 < τ₀.im)
    (hmax : ∀ τ : ℂ, charPoly params13 τ = 0 → 0 < τ.im → τ.re ≤ τ₀.re) :
    (227.58019641 ≤ C0 params13 τ₀ ∧ C0 params13 τ₀ < 227.58019642) ∧
      (226.24944266 ≤ C1 params13 ∧ C1 params13 < 226.24944267) ∧
      C1 params13 < C0 params13 τ₀ := by sorry
end ZudilinZeta
