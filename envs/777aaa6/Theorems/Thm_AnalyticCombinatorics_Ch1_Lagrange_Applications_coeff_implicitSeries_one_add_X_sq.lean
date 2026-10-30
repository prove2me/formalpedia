-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_Lagrange_Applications_coeff_implicitSeries_one_add_X_sq
-- name    : AnalyticCombinatorics.Ch1.Lagrange.Applications.coeff_implicitSeries_one_add_X_sq
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T11:35:36.772126+00:00
-- url     : https://prove2.me/theorems/4a1cfa9a-38e6-4178-9a36-0f464f04b2d5
-- title:
--   Catalan coefficients of the quadratic implicit series
-- statement:
--   Let $T\in\mathbb Q[[z]]$ be the source implicit series for $\Phi(t)=(1+t)^2$, characterized by $T(0)=0$ and $T=z(1+T)^2$. For every integer $n>0$,
--
--   $$[z^n]T(z)=\operatorname{Catalan}_n.$$
--
--   The Catalan number is the source `Nat.catalan n`, coerced to $\mathbb Q$; the theorem retains $n>0$.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/Lagrange/Applications.lean#L58. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

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

theorem AnalyticCombinatorics.Ch1.Lagrange.Applications.coeff_implicitSeries_one_add_X_sq (n : ℕ) (hn : 0 < n) :
    coeff n (ImplicitSeries.implicitSeries ((1 + X)^2 : ℚ⟦X⟧)) = Nat.catalan n := by sorry
