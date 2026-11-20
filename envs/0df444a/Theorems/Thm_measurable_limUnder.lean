-- Prove2me | Theorems.Thm_measurable_limUnder
-- name    : measurable_limUnder
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:56:28.122569+00:00
-- url     : https://prove2.me/theorems/6c0f4f09-e665-4406-9cb0-f8bbacc12d87
-- title:
--   measurable limUnder
-- statement:
--   The source theorem `measurable_limUnder` is extracted from `BrownianMotion.Continuity.LimitModification`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_LimitModification_F000

/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
#

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section aux

theorem measurable_limUnder {ι X E : Type*} [MeasurableSpace X] [TopologicalSpace E] [PolishSpace E]
    [MeasurableSpace E] [BorelSpace E] [Countable ι] {l : Filter ι}
    [l.IsCountablyGenerated] {f : ι → X → E} [hE : Nonempty E] (hf : ∀ i, Measurable (f i)) :
    Measurable (fun x ↦ limUnder l (f · x)) := by sorry
