-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch5_ContinuedFractions_coeff_JFraction_height_indep
-- name    : AnalyticCombinatorics.Ch5.ContinuedFractions.coeff_JFraction_height_indep
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-25T15:44:12.225293+00:00
-- url     : https://prove2.me/theorems/67b17656-eb89-4e19-942e-f6772768805a
-- title:
--   Finite J-fraction coefficients stabilize above their degree
-- statement:
--   Let $R$ be any commutative ring and let $a,b,c:\mathbb N\to R$ be arbitrary weights. Write $(\sigma a)(k)=a(k+1)$, and similarly for $b,c$. Define finite formal J-fractions by $J_0(a,b,c)=1/(1-c(0)z)$ and $J_{h+1}(a,b,c)=1/(1-c(0)z-a(0)b(0)z^2J_h(\sigma a,\sigma b,\sigma c))$, where reciprocals are formal inverses of series with constant term one. For $h,n\in\mathbb N$ with $n\le h$,
--
--   $$[z^n]J_h(a,b,c)=[z^n]J_n(a,b,c).$$
--
--   There are no positivity assumptions on the weights. This is coefficientwise stability of finite-height series; it neither defines an infinite continued fraction nor asserts analytic convergence.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch5/ContinuedFractions/FlajoletUnbounded.lean#L82. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch5_ContinuedFractions_Flajolet
import Mathlib

namespace AnalyticCombinatorics.Ch5.ContinuedFractions.PathSum end AnalyticCombinatorics.Ch5.ContinuedFractions.PathSum

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Ch5 §V — Flajolet's continued fraction theorem: removing the height bound

`Flajolet.lean` / `FlajoletPathSum.lean` prove the **bounded-height** form
`flajolet_cf` / `coeff_JFraction_eq_pathSum`: for every height bound `h`, the
height-`h` J-fraction's coefficients are the height-`h` Motzkin path sums.

The bound is immaterial for the coefficient of `z^n`: a Motzkin path of length
`n` (which returns to level 0) can never reach relative height above `n`, so the
length-`n` coefficient stabilizes once `h ≥ n`. This file proves that
stabilization, lifting the theorem off the height restriction:

* `Wcoeff_height_indep` — `Wcoeff h a b c n = Wcoeff k a b c n` whenever
  `n ≤ h` and `n ≤ k` (the coefficient is independent of the height bound
  above the length).
* `coeff_JFraction_height_indep` — the height-`h` J-fraction's `z^n` coefficient
  equals the height-`n` one for any `h ≥ n`; i.e. the bounded J-fraction agrees
  with the full (unbounded) continued fraction in every coefficient.
-/

open scoped BigOperators PowerSeries

open AnalyticCombinatorics AnalyticCombinatorics.Ch5 AnalyticCombinatorics.Ch5.ContinuedFractions
open AnalyticCombinatorics.Ch5.ContinuedFractions.PathSum

theorem AnalyticCombinatorics.Ch5.ContinuedFractions.coeff_JFraction_height_indep {R : Type*} [CommRing R]
    (h n : ℕ) (a b c : ℕ → R) (hn : n ≤ h) :
    PowerSeries.coeff (R := R) n (JFraction h a b c)
      = PowerSeries.coeff (R := R) n (JFraction n a b c) := by sorry
