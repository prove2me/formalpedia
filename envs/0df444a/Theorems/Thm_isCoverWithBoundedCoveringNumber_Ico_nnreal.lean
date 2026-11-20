-- Prove2me | Theorems.Thm_isCoverWithBoundedCoveringNumber_Ico_nnreal
-- name    : isCoverWithBoundedCoveringNumber_Ico_nnreal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:45:18.92452+00:00
-- url     : https://prove2.me/theorems/85938ae7-5dfb-47de-9d63-adfe6f7cca60
-- title:
--   isCoverWithBoundedCoveringNumber Ico nnreal
-- statement:
--   The source theorem `isCoverWithBoundedCoveringNumber_Ico_nnreal` is extracted from `BrownianMotion.Continuity.HasBoundedInternalCoveringNumber`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_HasBoundedInternalCoveringNumber_F001

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# HasBoundedCoveringNumber

-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal

variable {T : Type*} [PseudoEMetricSpace T] {A : Set T} {c : ℝ≥0∞} {ε : ℝ≥0} {d : ℝ}

set_option backward.isDefEq.respectTransparency false in
open scoped Pointwise in
theorem isCoverWithBoundedCoveringNumber_Ico_nnreal :
    IsCoverWithBoundedCoveringNumber (fun n ↦ Set.Ico (0 : ℝ≥0) (n + 1)) Set.univ
      (fun n ↦ 3 * (n + 1)) (fun _ ↦ 1) := by sorry
