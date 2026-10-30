-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_erdos_limit_constant_of_asymptotics
-- name    : AnalyticCombinatorics.Ch8.Partitions.erdos_limit_constant_of_asymptotics
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T15:17:25.833828+00:00
-- url     : https://prove2.me/theorems/73a5051f-a58e-47e9-9bab-d3bcb2fd1433
-- title:
--   Supporting lemma: erdos limit constant of asymptotics
-- statement:
--   **Brick 5 (combination).** Given the Abelian comparison (brick 3,
--   `log P − log a − log modelSaddle → 0`) and the real-saddle asymptotic (brick 4,
--   `log modelSaddle − A/t − ½log t − log(4√π/C) → 0`), together with the second-order
--   Laplace law (brick 2, `log_partLaplace_second_order`), the Erdős limit constant is
--   `a = 1/(4√3)`.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem erdos_limit_constant_of_asymptotics
--       {a : ℝ} (ha : 0 < a)
--       (hB3 :
--         Tendsto
--           (fun t : ℝ => Real.log (PartLaplace t) - Real.log a - Real.log (modelSaddle t))
--           (𝓝[>] (0 : ℝ)) (𝓝 0))
--       (hB4 :
--         Tendsto
--           (fun t : ℝ =>
--             Real.log (modelSaddle t) - A / t - (1 / 2 : ℝ) * Real.log t
--               - Real.log (4 * Real.sqrt Real.pi / C))
--           (𝓝[>] (0 : ℝ)) (𝓝 0)) :
--       a = 1 / (4 * Real.sqrt 3)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/ErdosConstant.lean#L97. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_LaplaceAsymptotic
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosConstant
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

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions

open Filter Topology Real
open AnalyticCombinatorics.Ch8.Partitions.Erdos

theorem AnalyticCombinatorics.Ch8.Partitions.erdos_limit_constant_of_asymptotics
    {a : ℝ} (ha : 0 < a)
    (hB3 :
      Tendsto
        (fun t : ℝ => Real.log (PartLaplace t) - Real.log a - Real.log (modelSaddle t))
        (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hB4 :
      Tendsto
        (fun t : ℝ =>
          Real.log (modelSaddle t) - A / t - (1 / 2 : ℝ) * Real.log t
            - Real.log (4 * Real.sqrt Real.pi / C))
        (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    a = 1 / (4 * Real.sqrt 3) := by sorry
