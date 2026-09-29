-- Prove2me | solution 1 for TangledSoundness.iterExt_selfLoop_ncard
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:50:38.340656+00:00
-- url     : https://prove2.me/submissions/c4740950-82f8-4d16-83d3-544247bb5487

-- Sol generated from Logic/ProvabilityLogic/SoundnessTopology.lean
import Mathlib
import Definitions.Def_Logic_ProvabilityLogic_SoundnessTopology
import Definitions.Def_Logic_ProvabilityLogic_TangledSoundness
import Theorems.Thm_TangledSoundness_soundnessExt_selfLoop_set
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



@[simp] theorem iterExt_succ (F : KFrame) (n : ℕ) :
    iterExt F (n + 1) = (iterExt F n).soundnessExt := rfl









-- !-- Lab Notes -- !--
--
-- Hypothesis (Hypothesizer):
--   H6. `μX.□X` is not merely "everything on GL frames" but *exactly* the well-founded
--       part of an arbitrary frame; hence the tangled core is a fixed-point-theoretic
--       invariant.
--   H7. The failure of levels caused by internal soundness is absolute: no ordinal,
--       indeed no well-founded, rank survives.
--   H8. (Bold, cross-domain) Internal soundness at every world plus positive
--       introspection is *equivalent* to the provability operator being a topological
--       interior operator — modal self-soundness = Alexandrov topology.
--   H9. (Quantitative) Iterating the soundness extension costs exactly one strange
--       loop per stage, and never reaches global self-soundness.
--
-- Experiment (Experimenter):
--   • H6: `lfp_boxOp_eq_accSet`. `≤` is Knaster–Tarski against the fixed point
--     `boxOp (Acc) = Acc` (Cycle 1's `boxOp_accSet`); `≥` is `Acc.rec` plus
--     `OrderHom.map_lfp`.  Corollary `sound_notMem_lfp_boxOp`.
--   • H7: `no_wf_rank_of_selfLoop` — a self-loop yields `s (rank w) (rank w)`, refuted
--     by `WellFounded.irrefl`.  Instantiated at `Ordinal` via `wellFounded_lt`.
--   • H8: `frameTopology` (opens = R-closed sets) is a genuine `TopologicalSpace`;
--     `isOpen_boxOp` needs transitivity, `interior_maximal` needs reflexivity, and the
--     converses are the two one-line valuation tricks `selfLoop_of_boxOp_subset`
--     (`X := R w ·`) and `trans_of_boxOp_idem` (`X := R u ·`).  `boxOp_eq_interior_iff`
--     packages both directions; `glFrame_boxOp_ne_interior` is the GL corner case.
--   • H9: `soundnessExt_selfLoop_set` computes the loop set of an extension as
--     `insert none (some '' old)`; `Set.ncard_insert_of_not_mem` plus
--     `Set.ncard_image_of_injective` give `ncard = n` by induction (finiteness is
--     carried along in the induction, since the base loop set is empty).
--     `iterExt_has_irrefl_world` (induction, transporting a witness along `some`)
--     yields `iterExt_has_unsound_world`.
--
-- Analysis (Analyst):
--   Survived: H6–H9, all sorry-free.  Structural pattern: *every* obstruction found in
--   this domain is the same obstruction seen through a different functor — the
--   self-loop is (i) a failure of accessibility (`lfp_boxOp_eq_accSet`), (ii) a failure
--   of ranking (`no_wf_rank_of_selfLoop`), and (iii) the presence of reflexivity that
--   topology demands (`boxOp_eq_interior_iff`).  The quantitative result H9 explains
--   *why* Tarski-style stratification feels endless: each metalevel adds exactly one
--   sound world and leaves the rest of the tower unsound, so the sound set has ncard
--   `n` while the tower keeps an irreflexive witness at every stage.
--   Needed a different definition: an early attempt to count "sound worlds" via
--   `Fintype.card` failed because the base frame may be infinite; `Set.ncard` of the
--   loop *set* is the right invariant, and it is finite even over infinite bases.
--
-- Critique (Critic):
--   `frameTopology` is not vacuous — its interior really is computed by `boxOp` on
--   reflexive transitive frames — and `boxOp_eq_interior_iff` is a genuine
--   biconditional, not a one-way implication dressed up.  The counting theorems are
--   guarded by the irreflexivity hypothesis on the base frame (satisfied by every GL
--   frame, `GLFrame.irrefl`), without which the count is false — the boundary is
--   stated explicitly rather than hidden.  `reflection_tower_report` combines only
--   previously established results and does not reference itself.
--
-- Synthesis (PI):
--   Internal soundness is a single geometric defect — reflexivity — with three faces:
--   fixed-point (outside `μX.□X`), order-theoretic (no rank), and topological
--   (interior semantics).  Stratifying adds one such defect per level and never
--   finishes.  See `FUTURE_DIRECTIONS.md`.
-- !-- Lab Notes -- !--
open TangledSoundness in
theorem solution(F : KFrame) (hirr : ∀ w : F.W, ¬ F.R w w) (n : ℕ) :
    {x : (iterExt F n).W | (iterExt F n).R x x}.Finite ∧
      {x : (iterExt F n).W | (iterExt F n).R x x}.ncard = n := by
  induction n with
  | zero =>
      have h0 : {x : (iterExt F 0).W | (iterExt F 0).R x x} = ∅ := by
        ext x
        constructor
        · intro h
          exact hirr x h
        · exact fun h => absurd h (Set.notMem_empty x)
      rw [h0]
      exact ⟨Set.finite_empty, Set.ncard_empty _⟩
  | succ n ih =>
      obtain ⟨hfin, hcard⟩ := ih
      rw [iterExt_succ, soundnessExt_selfLoop_set]
      have hinj : Function.Injective (some : (iterExt F n).W → Option (iterExt F n).W) :=
        Option.some_injective _
      have himfin : (some '' {x : (iterExt F n).W | (iterExt F n).R x x}).Finite :=
        hfin.image _
      have hnotmem : (none : Option (iterExt F n).W)
          ∉ some '' {x : (iterExt F n).W | (iterExt F n).R x x} := by
        simp
      refine ⟨himfin.insert _, ?_⟩
      calc (insert none (some '' {x : (iterExt F n).W | (iterExt F n).R x x})).ncard
          = (some '' {x : (iterExt F n).W | (iterExt F n).R x x}).ncard + 1 :=
            Set.ncard_insert_of_notMem hnotmem himfin
        _ = {x : (iterExt F n).W | (iterExt F n).R x x}.ncard + 1 :=
            by rw [Set.ncard_image_of_injective _ hinj]
        _ = n + 1 := by rw [hcard]
