-- Prove2me | Theorems.Thm_TangledSoundness_soundnessExt_selfLoop_set
-- name    : TangledSoundness.soundnessExt_selfLoop_set
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:47:14.232741+00:00
-- url     : https://prove2.me/theorems/566d105f-450e-421a-b9fe-c3874f479840
-- title:
--   The self-loops of a soundness extension: the new top, plus the old loops.
-- statement:
--   The self-loops of a soundness extension: the new top, plus the old loops.
--
--   ```lean
--   theorem TangledSoundness.soundnessExt_selfLoop_set(G : KFrame) :
--       {x : (G.soundnessExt).W | (G.soundnessExt).R x x}
--         = insert none (some '' {x : G.W | G.R x x}) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/ProvabilityLogic/SoundnessTopology.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/ProvabilityLogic/SoundnessTopology.lean#L220

-- Thm stub generated from Logic/ProvabilityLogic/SoundnessTopology.lean
import Mathlib
import Definitions.Def_Logic_ProvabilityLogic_SoundnessTopology
import Definitions.Def_Logic_ProvabilityLogic_TangledSoundness
/-
# Cycle 2: The Geometry of Self-Soundness — Fixed Points, Topology, and the
# Reflection Tower

Cycle 1 (`Logic.ProvabilityLogic.TangledSoundness`) proved that a world validating
its own soundness schema is exactly a self-accessing world, and that soundness and
Löb are jointly unsatisfiable.  This second cycle asks *where* the tangle sits, *what*
structure it destroys, and *how fast* it grows when one tries to escape by
stratification.

## Main results

* `lfp_boxOp_eq_accSet` — **the least fixed point of the provability operator is
  exactly the well-founded part of the frame.**  A sharpening of the fixed-point form
  of Löb's theorem (`lfp_boxOp_eq_univ_iff_wf`): `μX.□X` is the set of converse
  accessible worlds, so the "tangled core" is precisely the complement of a modal
  fixed point.
* `sound_notMem_lfp_boxOp` — a world that internalises its soundness lies outside
  `μX.□X`; internal soundness is invisible to every Löb-style induction.
* `uniformlySound_no_wf_rank`, `uniformlySound_no_ordinal_grading` — the collapse of
  levels is not a ℕ-artefact: a sound world admits **no** rank into any well-founded
  order, ordinals included.
* `boxOp_eq_interior_iff` — **cross-domain bridge (modal logic ↔ topology).**  The box
  operator of a frame is the topological interior operator of its Alexandrov topology
  **iff** every world internalises its own soundness *and* the frame is transitive
  (positive introspection).  So "interior semantics for provability" and "internal
  soundness everywhere" are the same hypothesis, and `glFrame_boxOp_ne_interior` shows
  no nonempty GL frame can have it.
* `iterExt_selfLoop_ncard`, `iterExt_sound_ncard` — **the reflection tower.**  Adding
  a soundness world `n` times produces a frame with exactly `n` self-loops and exactly
  `n` sound worlds: each reflection step costs precisely one strange loop.
* `iterExt_has_unsound_world` — **stratification never converges.**  No finite number
  of reflection steps makes the whole hierarchy internally sound.

## Relationship to catalog
Extends `Logic.ProvabilityLogic.TangledSoundness` (Cycle 1) and, through it,
`Logic.ProvabilityLogic.GLPFrames` and `Logic.TangledHierarchies`.
-/


open TangledSoundness

open GLPLogic

universe u

variable {α : Type*}

/-! ## Part A — The least fixed point of the box operator is the well-founded part -/





/-! ## Part B — No grading at all, not merely no ℕ-grading -/




/-! ## Part C — Cross-domain bridge: box as a topological interior operator

A Kripke frame carries a canonical (Alexandrov) topology whose open sets are the
`R`-closed sets.  The box operator is the interior operator of this topology exactly
when the system internalises its soundness everywhere and is positively
introspective. -/








/-! ## Part D — The reflection tower: one loop per stage -/

theorem TangledSoundness.soundnessExt_selfLoop_set(G : KFrame) :
    {x : (G.soundnessExt).W | (G.soundnessExt).R x x}
      = insert none (some '' {x : G.W | G.R x x}) := by sorry
