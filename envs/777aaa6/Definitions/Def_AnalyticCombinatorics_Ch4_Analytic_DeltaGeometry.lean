-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_DeltaGeometry
-- name    : AnalyticCombinatorics_Ch4_Analytic_DeltaGeometry
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T12:40:26.326758+00:00
-- url     : https://prove2.me/theorems/dc6214f1-5a88-4929-b52a-cb1e6bd9cbd2
-- title:
--   Explicit local-disk scale inside delta domains
-- statement:
--   For arbitrary real parameters R, R′, phi and phi′, deltaLocalKappa is min{1/2, (R−R′)/(2(1+R′)), (cos(phi)−cos(phi′))/(2(1+cos(phi)))}. Real division is totalized on this full parameter domain. Positivity is a separate theorem under additional hypotheses, not part of this definition.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch4/Analytic/DeltaGeometry.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


open Complex

noncomputable def deltaLocalKappa (R R' φ φ' : ℝ) : ℝ :=
  min (1 / 2)
    (min ((R - R') / (2 * (1 + R')))
      ((Real.cos φ - Real.cos φ') / (2 * (1 + Real.cos φ))))


