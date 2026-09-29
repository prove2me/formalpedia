-- Prove2me | solution 1 for TangledSoundness.twoChain_converse_wf
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:59:32.218989+00:00
-- url     : https://prove2.me/submissions/6655d7fd-4dbc-418a-8ae8-af5d0c3733e2

-- Sol generated from Logic/ProvabilityLogic/IteratedReflection.lean
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











/-! ## Part C — Realising the spectrum: cycle frames -/







/-! ## Part D — The boundary: consistency is free -/









-- !-- Lab Notes -- !--
--
-- Hypothesis (Hypothesizer):
--   H10. Reflection restricted to propositional *atoms* already forces the tangle, so
--        the soundness schema has no affordable fragment.
--   H11. (Bold) `n`-fold reflection `□ⁿφ → φ` is equivalent to lying on a cycle of
--        length exactly `n`: internal soundness is *graded by cycle length*.
--   H12. (Bold) The grading is strict and realised: cycle frames `ZMod n` validate
--        degree `n` and refute every smaller positive degree, with no self-loops.
--   H13. Consistency `¬□⊥` sits strictly below the whole spectrum: it is satisfiable
--        on a loop-free converse well-founded frame.
--
-- Experiment (Experimenter):
--   • H10: `atomicSound_iff_uniformlySound` — the Cycle-1 valuation `p ↦ R w ·` only
--     ever used a variable, so the atomic fragment suffices; the converse is trivial.
--   • H11: `sat_boxIter` (induction on `n`, `iterR` bookkeeping) turns `□ⁿφ` into a
--     statement about `n`-step reachability; then the same valuation trick, now with
--     `p ↦ iterR F n w ·`, gives `iterSound_iff_cycle`.
--   • H12: `cycleFrame_iterR` (induction, `push_cast; ring`) computes `k`-step
--     accessibility in `ZMod n` as `+k`; degree `n` holds by `ZMod.natCast_self`, and
--     failure for `0 < k < n` reduces to `n ∤ k` via `ZMod.natCast_eq_zero_iff`.
--   • H13: `twoChain` with explicit `Acc` witnesses; `sat_con_iff` identifies internal
--     consistency with seriality.
--
-- Analysis (Analyst):
--   Survived: H10–H13, sorry-free.  Structural pattern: *the modal degree of a
--   reflection principle equals the combinatorial girth it forces.*  Degree 1 forces a
--   loop (Cycle 1), degree n forces an n-cycle, degree 0 forces nothing (`iterR 0` is
--   equality, and indeed `□⁰φ → φ` is a tautology), and consistency is not a
--   reflection principle at all — it forces only seriality, which well-founded frames
--   supply freely.  This explains, semantically, why consistency statements are
--   comparatively cheap while reflection principles are not.
--   Corner case found by testing: for `n = 1` the "cycle frame" `ZMod 1` is a single
--   reflexive world, so `cycleFrame_no_selfLoop` genuinely needs `2 ≤ n`; the
--   hypothesis is stated rather than hidden.
--
-- Critique (Critic):
--   `soundness_degree_spectrum` is not vacuous: it exhibits a concrete frame with a
--   positive property (degree-`n` soundness) alongside the negative ones, and the
--   `NeZero n` instance is derived from `2 ≤ n` rather than assumed.  No theorem is
--   `rfl`-only: the interesting content of `iterSound_iff_cycle` is the valuation
--   construction, and of `cycleFrame_not_iterSound_lt` the divisibility argument.
--   `consistency_vs_reflection_boundary` only assembles previously proved results.
-- !-- Lab Notes -- !--
open TangledSoundness in
theorem solution: WellFounded (Function.swap twoChain.R) := by
  have hfalse : Acc (Function.swap twoChain.R) false := by
    refine Acc.intro false ?_
    rintro y ⟨hy, -⟩
    exact absurd hy (by simp)
  refine ⟨fun x => ?_⟩
  cases x with
  | false => exact hfalse
  | true =>
      refine Acc.intro true ?_
      rintro y ⟨-, rfl⟩
      exact hfalse
