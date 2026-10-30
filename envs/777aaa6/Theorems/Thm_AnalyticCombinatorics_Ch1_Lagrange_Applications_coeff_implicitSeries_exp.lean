-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_Lagrange_Applications_coeff_implicitSeries_exp
-- name    : AnalyticCombinatorics.Ch1.Lagrange.Applications.coeff_implicitSeries_exp
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T11:35:37.578987+00:00
-- url     : https://prove2.me/theorems/21546cec-448c-4416-8976-438d8b627685
-- title:
--   Cayley coefficients of the exponential implicit series
-- statement:
--   Let $T\in\mathbb Q[[z]]$ be the source implicit series for $\Phi(t)=\exp(t)=\sum_{j\ge0}t^j/j!$, characterized by $T(0)=0$ and $T=z\exp(T)$. For each integer $n>0$,
--
--   $$[z^n]T(z)=\frac{n^{n-1}}{n!}.$$
--
--   The arithmetic is rational and the factorial normalization is retained. This coefficient identity does not itself construct a labelled-tree bijection.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/Lagrange/Applications.lean#L101. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_Lagrange_ImplicitSeries
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Applications of Lagrange inversion

This file records the Catalan and Cayley coefficient formulas obtained from
the formal Lagrange inversion theorem.
-/

namespace Nat

export _root_ (catalan)

end Nat

open AnalyticCombinatorics AnalyticCombinatorics.Ch1 AnalyticCombinatorics.Ch1.Lagrange

open PowerSeries

theorem AnalyticCombinatorics.Ch1.Lagrange.Applications.coeff_implicitSeries_exp (n : ℕ) (hn : 0 < n) :
    coeff n (ImplicitSeries.implicitSeries (PowerSeries.exp ℚ)) =
      (n : ℚ) ^ (n - 1) / n.factorial := by sorry
