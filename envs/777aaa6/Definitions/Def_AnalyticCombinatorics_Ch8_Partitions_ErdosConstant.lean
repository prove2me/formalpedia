-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosConstant
-- name    : AnalyticCombinatorics_Ch8_Partitions_ErdosConstant
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T15:13:39.146394+00:00
-- url     : https://prove2.me/theorems/520677e6-cb24-4280-a0c7-7914c52a9854
-- title:
--   Erdos Constant mathematical objects
-- statement:
--   modelSaddle(t) is the infinite sum of exp(Csqrt(n)-tn)/n over natural indices, with the real inverse convention at0.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/ErdosConstant.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Hardy–Ramanujan constant: brick 5 algebra (HR constant avenue d)

The pure-`√` constant identity underlying `a = 1/(4√3)`:
`(4√π / C)·√(2π) = 4√3`, where `C = π√(2/3)` and `C² = 4A = 2π²/3`.

This is the arithmetic core that bricks 2–4 feed into: with `K = 4√π/C` the saddle
prefactor and `√(2π)` the Meinardus prefactor, the limit constant is
`a = 1/(K·√(2π)) = 1/(4√3)`.
-/

namespace AnalyticCombinatorics.Ch8.Partitions

open Filter Topology Real
open AnalyticCombinatorics.Ch8.Partitions.Erdos

noncomputable section

/-- The 1-D real-saddle model sum `∑_{k≥1} e^{C√k − tk}/k` (the `k=0` term is `0`). -/
noncomputable def modelSaddle (t : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (C * Real.sqrt (n : ℝ) - t * (n : ℝ)) / (n : ℝ)

end

end AnalyticCombinatorics.Ch8.Partitions


