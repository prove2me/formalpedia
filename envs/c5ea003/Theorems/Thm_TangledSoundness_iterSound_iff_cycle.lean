-- Prove2me | Theorems.Thm_TangledSoundness_iterSound_iff_cycle
-- name    : TangledSoundness.iterSound_iff_cycle
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:48:13.140985+00:00
-- url     : https://prove2.me/theorems/e9286f81-c271-488a-8a60-9c4aa0218743
-- title:
--   The tangle spectrum theorem.
-- statement:
--   **The tangle spectrum theorem.**  A world validates the `n`-fold reflection
--   principle `□ⁿφ → φ` (uniformly in the valuation) **iff** it lies on a cycle of length
--   exactly `n`.  Internal soundness of degree `n` *is* an `n`-cycle.
--
--   ```lean
--   theorem TangledSoundness.iterSound_iff_cycle(F : KFrame) (p : α) (n : ℕ) (w : F.W) :
--       IterSoundAt F α n w ↔ iterR F n w w := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/ProvabilityLogic/IteratedReflection.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/ProvabilityLogic/IteratedReflection.lean#L101

-- Thm stub generated from Logic/ProvabilityLogic/IteratedReflection.lean
import Mathlib
import Definitions.Def_Logic_ProvabilityLogic_IteratedReflection
import Definitions.Def_Logic_ProvabilityLogic_SoundnessTopology
import Definitions.Def_Logic_ProvabilityLogic_TangledSoundness
/-
# Cycle 3: The Spectrum of Tangles — Iterated Reflection and Cycle Length

Cycles 1–2 showed that internalising the soundness schema `□φ → φ` at a world is
*equivalent* to a self-loop, and traced the consequences (no rank, no Löb fixed point,
no interior semantics, one loop per stratification step).  This cycle calibrates the
phenomenon: how *weak* can an internal soundness principle be before the tangle
disappears?

Two sharp answers:

* **From below the schema cannot be weakened.**  `atomicSound_iff_uniformlySound`:
  reflection for *propositional variables only* already forces the self-loop, hence
  the full reflection schema for all formulas.  There is no non-trivial fragment of
  soundness that a well-founded system can afford.
* **From above the tangle can be stretched, not removed.**  `iterSound_iff_cycle`:
  the `n`-fold reflection principle `□ⁿφ → φ` holds at `w` (uniformly) **iff** `w`
  lies on a cycle of length `n`.  The cycle frames `ZMod n` realise every point of
  this spectrum (`cycleFrame_iterSound_self`, `cycleFrame_not_iterSound_lt`), so
  internal soundness comes in a strictly increasing hierarchy of tangle lengths —
  but every one of them tangles the transitive closure
  (`iterSound_transGen_isTangled`) and none is available on a GL frame
  (`glFrame_no_iterSound`).
* **Where the boundary really is.**  Consistency (`¬□⊥`) is *not* on this spectrum:
  `twoChain` is converse well-founded, loop-free, and internally consistent
  (`twoChain_consistent_true`).  Consistency costs nothing; reflection costs a loop.

## Relationship to catalog
Extends `Logic.ProvabilityLogic.TangledSoundness` (Cycle 1) and
`Logic.ProvabilityLogic.SoundnessTopology` (Cycle 2); uses `GLFrame`, `MFormula` from
`Logic.ProvabilityLogic.GLPFrames` and `IsTangled` from `Logic.TangledHierarchies`.
-/


open TangledSoundness

open GLPLogic

universe u

variable {α : Type*}

/-! ## Part A — Atomic reflection already forces the loop -/



/-! ## Part B — `n`-step accessibility and `n`-fold reflection -/

theorem TangledSoundness.iterSound_iff_cycle(F : KFrame) (p : α) (n : ℕ) (w : F.W) :
    IterSoundAt F α n w ↔ iterR F n w w := by sorry
