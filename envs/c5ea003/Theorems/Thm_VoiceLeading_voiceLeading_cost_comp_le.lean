-- Prove2me | Theorems.Thm_VoiceLeading_voiceLeading_cost_comp_le
-- name    : VoiceLeading.voiceLeading_cost_comp_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:29:16.127403+00:00
-- url     : https://prove2.me/theorems/44945527-2b4a-40dd-b7ba-af2a66412242
-- title:
--   Triangle inequality for voice-leading cost: the cost of a composed
-- statement:
--   **Triangle inequality for voice-leading cost**: the cost of a composed
--   voice-leading is at most the sum of the individual costs.
--
--   ```lean
--   theorem VoiceLeading.voiceLeading_cost_comp_le{n : ℕ} {V W U : Voicing n}
--       (f : VL n V W) (g : VL n W U) :
--       (f.comp g).cost ≤ f.cost + g.cost := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/VoiceLeadingCategory.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/VoiceLeadingCategory.lean#L82

-- Thm stub generated from Bridges/VoiceLeadingCategory.lean
import Mathlib
import Definitions.Def_Bridges_VoiceLeadingCategory

/-!
# Categorical Voice-Leading Geometry

This file defines a category of voice-leadings between equal-cardinality pitch-class
configurations and proves that voice-leading cost satisfies the triangle inequality,
making it a functor into Lawvere metric spaces (enriched categories over [0,∞]).

## Main Results

* `VoiceLeading.cost_id` — Identity voice-leading has zero cost
* `voiceLeading_cost_comp_le` — **Triangle inequality**: cost of composition ≤ sum of costs
* `vlDist_triangle` — Triangle inequality for minimum voice-leading distance
* `vlLawvere` — Voice-leadings form a Lawvere metric space

## Mathematical Significance

Voice-leading — the art of moving smoothly between chords — is shown to be
not merely a musical heuristic but a **functorial distance theory**. The cost
of a voice-leading (sum of pitch displacements) satisfies the enriched
composition law of a Lawvere metric space. This creates a formal bridge between
music theory, enriched category theory, and optimal transport.
-/

open Finset BigOperators CategoryTheory

noncomputable section

open VoiceLeading

/-! ## Core Definitions -/


instance (n : ℕ) : Inhabited (Voicing n) := ⟨fun _ => 0⟩





/-! ## Cost Properties -/

theorem VoiceLeading.voiceLeading_cost_comp_le{n : ℕ} {V W U : Voicing n}
    (f : VL n V W) (g : VL n W U) :
    (f.comp g).cost ≤ f.cost + g.cost := by sorry
