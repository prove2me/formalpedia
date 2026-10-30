-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch2_Mappings_RamanujanQ
-- name    : AnalyticCombinatorics_Ch2_Mappings_RamanujanQ
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T09:48:05.601553+00:00
-- url     : https://prove2.me/theorems/826fb0bd-b1ea-4290-99a0-6423bcb8c81e
-- title:
--   The finite Ramanujan sum and Gaussian comparison kernel
-- statement:
--   For natural numbers $n,k$, define $T_{n,k}=\prod_{j=1}^{k}(1-j/n)$ over the real numbers, with empty product one, and define $Q(n)=\sum_{k=0}^{n-1}T_{n,k}$. The empty sum gives $Q(0)=0$. The comparison kernel is $\exp(-x^2/(2n))$ for real $x$. Division is totalized at zero in these definitions; bounds involving decay are stated separately with their positivity hypotheses.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/Mappings/RamanujanQ.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Ramanujan's Q-function for random mappings

This file defines the finite Ramanujan Q-function from Flajolet--Sedgewick,
Chapter II.3.  The intended asymptotic is

`Q(n) ~ sqrt (pi * n / 2)`.

The full Laplace-method asymptotic is not yet present in Mathlib.  This file
records the faithful finite definition and elementary verified bounds that are
used by that proof.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS

noncomputable section

/-- The `k`-th summand in Ramanujan's Q-function.  The empty product is `1`. -/
def ramanujanQTerm (n k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, (1 - (((j + 1 : ℕ) : ℝ) / (n : ℝ)))

/--
Ramanujan's Q-function:

`Q(n) = 1 + (1 - 1/n) + (1 - 1/n)(1 - 2/n) + ...`.

For `n = 0` the finite sum is empty, which is harmless for asymptotic uses.
-/
def ramanujanQ (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, ramanujanQTerm n k

/-- The Gaussian kernel that dominates the summands of `ramanujanQ`. -/
def gaussianKernel (n : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-((n : ℝ)⁻¹ * 2⁻¹ * x ^ 2))

end

end AnalyticCombinatorics.Ch2.Mappings.RamanujanQNS


