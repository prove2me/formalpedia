-- Prove2me | solution 1 for TangledSoundness.boxOp_eq_interior_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:44:14.510462+00:00
-- url     : https://prove2.me/submissions/85a68e3f-a5e2-4ea2-bfa4-d714b93a9785

-- Sol generated from Logic/ProvabilityLogic/SoundnessTopology.lean
import Mathlib
import Definitions.Def_Logic_ProvabilityLogic_SoundnessTopology
import Definitions.Def_Logic_ProvabilityLogic_TangledSoundness
import Theorems.Thm_TangledSoundness_uniformlySound_iff_selfLoop
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


/-- `boxOp F X` is open when the frame is transitive. -/
theorem isOpen_boxOp (F : KFrame)
    (htrans : ∀ u v w : F.W, F.R u v → F.R v w → F.R u w) (X : Set F.W) :
    (frameTopology F).IsOpen (boxOp F X) := by
  intro w hw v hv u hu
  exact hw u (htrans w v u hv hu)

/-- Reflexivity is forced by `□X ⊆ X`: the semantic soundness schema on subsets. -/
theorem selfLoop_of_boxOp_subset (F : KFrame) (h : ∀ X : Set F.W, boxOp F X ⊆ X)
    (w : F.W) : F.R w w :=
  h {v | F.R w v} (fun _ hv => hv)

/-- Transitivity is forced by idempotence of the box operator: the semantic form of
positive introspection `□X ⊆ □□X`. -/
theorem trans_of_boxOp_idem (F : KFrame)
    (h : ∀ X : Set F.W, boxOp F X ⊆ boxOp F (boxOp F X)) (u v w : F.W)
    (huv : F.R u v) (hvw : F.R v w) : F.R u w :=
  h {x | F.R u x} (fun _ hx => hx) v huv w hvw

/-- With reflexivity and transitivity, the box operator computes topological
interiors. -/
theorem interior_eq_boxOp (F : KFrame) (hrefl : ∀ w : F.W, F.R w w)
    (htrans : ∀ u v w : F.W, F.R u v → F.R v w → F.R u w) (X : Set F.W) :
    @interior F.W (frameTopology F) X = boxOp F X := by
  letI : TopologicalSpace F.W := frameTopology F
  apply le_antisymm
  · intro w hw v hv
    exact interior_subset (isOpen_interior (s := X) w hw v hv)
  · exact interior_maximal (fun w hw => hw w (hrefl w)) (isOpen_boxOp F htrans X)



/-! ## Part D — The reflection tower: one loop per stage -/












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
theorem solution(F : KFrame) (p : α) :
    (∀ X : Set F.W, @interior F.W (frameTopology F) X = boxOp F X) ↔
      ((∀ w : F.W, UniformlySoundAt F α w) ∧
        ∀ u v w : F.W, F.R u v → F.R v w → F.R u w) := by
  letI : TopologicalSpace F.W := frameTopology F
  constructor
  · intro h
    have hsub : ∀ X : Set F.W, boxOp F X ⊆ X := by
      intro X
      rw [← h X]
      exact interior_subset
    have hidem : ∀ X : Set F.W, boxOp F X ⊆ boxOp F (boxOp F X) := by
      intro X
      rw [← h X, ← h (interior X)]
      exact interior_maximal (fun _ hw => hw) isOpen_interior
    refine ⟨fun w => ?_, trans_of_boxOp_idem F hidem⟩
    exact (uniformlySound_iff_selfLoop F p w).mpr (selfLoop_of_boxOp_subset F hsub w)
  · rintro ⟨hsound, htrans⟩
    intro X
    exact interior_eq_boxOp F
      (fun w => (uniformlySound_iff_selfLoop F p w).mp (hsound w)) htrans X
