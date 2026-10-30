-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_RamanujanQSharp
-- name    : AnalyticCombinatorics_Ch2_Mappings_RamanujanQSharp
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T09:48:01.556839+00:00
-- url     : https://prove2.me/theorems/76c2b848-697d-4ab5-99f4-6932a9264921
-- title:
--   Auxiliary real coefficients and Gaussian functions for lower comparison
-- statement:
--   For natural numbers $m,n$ and real $x$, define $c_m=(m+1)/m$ and $G_{m,n}(x)=\exp(-c_m x^2/(2n))$. These auxiliary coefficients and Gaussian functions support lower comparisons for the finite Ramanujan sum. The definitions use totalized real division, so $c_0=0$ and $G_{m,n}$ is identically one when $m=0$ or $n=0$; positivity restrictions belong to the separate bounds.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/Mappings/RamanujanQSharp.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Sharp lower asymptotic for Ramanujan's Q-function

This file proves the missing lower comparison for Ramanujan's finite
`Q`-function and upgrades the previously banked upper bound to the sharp
equivalence `Q(n) ~ sqrt (pi * n / 2)`.
-/

open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

noncomputable section

namespace Sharp

def lowerCoeff (m : ℕ) : ℝ :=
  (((m + 1 : ℕ) : ℝ) / (m : ℝ))

def lowerGaussian (m n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-((lowerCoeff m / (2 * (n : ℝ))) * x ^ 2))

end Sharp

end

end AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS


