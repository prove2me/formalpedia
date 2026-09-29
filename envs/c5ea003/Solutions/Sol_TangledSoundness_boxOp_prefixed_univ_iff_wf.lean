-- Prove2me | solution 1 for TangledSoundness.boxOp_prefixed_univ_iff_wf
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:44:15.124867+00:00
-- url     : https://prove2.me/submissions/61c5986f-35b7-4cd5-a976-fb06febb09b0

-- Sol generated from Logic/ProvabilityLogic/TangledSoundness.lean
import Mathlib
import Definitions.Def_Logic_ProvabilityLogic_GLPFrames
import Definitions.Def_Logic_ProvabilityLogic_TangledSoundness
import Definitions.Def_Logic_TangledHierarchies
import Theorems.Thm_TangledSoundness_boxOp_accSet
/-
# Tangled Hierarchies: Proof Systems That Reference Their Own Soundness

A proof system "references its own soundness" when the reflection schema
`□φ → φ` — *whatever is provable is true* — is available **inside** the system it
validates.  On the Kripke side this is the *reflection (soundness) schema* holding at
a world of a frame.  This file proves that internalised soundness is **exactly** a
strange loop: a world validates its own soundness schema iff it accesses itself, and
therefore no well-founded (GL / provability) hierarchy can host a sound world.

## Main results

* `uniformlySound_iff_selfLoop` — **soundness = tangle.**  A world `w` of a Kripke
  frame validates every instance `□φ → φ` (for every valuation) **iff** `R w w`.
* `loebAt_irrefl` — a world validating every Löb instance is irreflexive.
* `no_sound_loeb_world`, `sound_loeb_frame_isEmpty` — **the tangle is unavoidable:**
  no world can validate both soundness and Löb; a frame validating both schemas is
  empty.  This is the semantic form of Gödel's second incompleteness theorem for
  the full reflection schema.
* `uniformlySound_isTangled`, `uniformlySound_no_grading` — a frame with a sound
  world is `TangledHierarchies.IsTangled` and admits **no** ℕ-valued level grading:
  the hierarchy of levels must genuinely collapse.
* `soundnessExt_*` — **the cost is exactly one loop.**  Every frame extends to one
  with a sound world (`KFrame.soundnessExt`), the extension preserves all truths of
  the original (generated-submodel truth lemma `soundnessExt_sat_some`), and it
  contains exactly one self-loop and exactly one sound world.
* `lfp_boxOp_eq_univ_iff_wf` — **modal fixed points.**  The least fixed point of the
  box operator on `Set W` is everything **iff** the frame is converse well-founded;
  `selfLoop_lfp_ne_univ` shows a single tangle destroys this fixed-point principle.
* `namesSoundness_two_world`, `serial_of_global_self_soundness`,
  `glFrame_isEmpty_of_global_self_soundness` — **the internal soundness predicate.**
  A frame can carry a propositional variable naming *its own* soundness set
  (a genuine modal fixed point, non-vacuous: some world sound, some not), but if the
  system asserts that predicate everywhere then every world has a successor, and a
  converse well-founded (GL) frame with a globally asserted soundness predicate is
  empty.

## Relationship to catalog
Builds on `Logic.ProvabilityLogic.GLPFrames` (`MFormula`, `GLFrame`, `forces`,
`loeb_valid`) and on `Logic.TangledHierarchies` (`IsTangled`, `HasSelfLoop`,
`tangled_has_no_grading`).  `GLFrame` is by construction converse well-founded, so
tangles are invisible there; the general `KFrame` here is the ambient category in
which the tangle can be exhibited, and `GLFrame.toKFrame` (with
`sat_toKFrame_eq_forces`) embeds the catalog's GL frames into it.
-/


open TangledSoundness

open GLPLogic

universe u

variable {α : Type*}

/-! ## Part 0 — General Kripke frames

`GLFrame` bakes in transitivity and converse well-foundedness, so it can never host a
tangle.  We work in the ambient class of *arbitrary* Kripke frames and embed GL frames
into it. -/









/-! ## Part 1 — The reflection (soundness) schema and the Löb schema -/











/-! ## Part 2 — Bridge: a sound world has no level grading -/




/-! ## Part 3 — The soundness extension: the cost is exactly one loop -/












/-! ## Part 4 — Modal fixed points: the box operator on subsets -/









/-! ## Part 5 — The soundness predicate *named inside* the language -/











-- !-- Lab Notes -- !--
--
-- Hypothesis (Hypothesizer):
--   H1. "A world validates its own soundness schema iff it is reflexive" — internal
--       soundness *is* a strange loop, not merely a cause of one.
--   H2. "Löb-validity at a world implies irreflexivity", so soundness and Löb are
--       jointly unsatisfiable at any single world (semantic Gödel 2, schema form).
--   H3. "The cost of internal soundness is exactly one tangle": every frame extends
--       conservatively to a frame with a unique sound world.
--   H4. (Fixed-point form) "μX.□X = ⊤ iff the frame is converse well-founded", so a
--       single self-loop annihilates the Löb fixed-point principle.
--   H5. (Bold) "A frame can carry a propositional variable naming exactly its own
--       soundness set" — weak internalisation is consistent — "but asserting that
--       variable globally forces seriality, hence emptiness on GL frames."
--
-- Experiment (Experimenter):
--   • H1: `uniformlySound_iff_selfLoop`. The ⇐ direction is immediate; ⇒ needs the
--     valuation `p ↦ R w ·`, which makes `□p` true at `w` for free, so `p` at `w`
--     must be `R w w`. One variable suffices.
--   • H2: `loebAt_irrefl`, valuation `p ↦ (· ≠ w)`. Checking `□(□p→p)` at `w` splits
--     on whether the successor equals `w`; both cases close.  `no_sound_loeb_world`
--     and `sound_loeb_frame_isEmpty` follow.
--   • H3: `KFrame.soundnessExt` (adjoin a reflexive top seeing everything);
--     `soundnessExt_sat_some` is the generated-submodel truth lemma (induction on
--     formulas; the box case uses that old worlds never see the new top).
--     `soundnessExt_sound_iff` gives uniqueness over irreflexive bases.
--   • H4: `boxOp_accSet` shows `Acc (swap R)` is *literally* a fixed point of the box
--     operator; that single observation yields both directions of
--     `boxOp_prefixed_univ_iff_wf`, and Knaster–Tarski (`OrderHom.map_lfp`,
--     `OrderHom.lfp_le`) upgrades it to `lfp_boxOp_eq_univ_iff_wf`.
--   • H5: `namesSoundness_two_world` on the 2-world frame `x R y ↔ y = t`: `t` is
--     reflexive hence sound, `f` is refuted by the single formula `s` itself
--     (`□s` holds at `f` because `f`'s only successor is `t`, but `s` fails at `f`).
--     `serial_of_global_self_soundness` uses the formula `¬s`;
--     `glFrame_isEmpty_of_global_self_soundness` combines it with a converse-minimal
--     world obtained from `WellFounded.has_min`.
--
-- Analysis (Analyst):
--   Survived: all five hypotheses, with no `sorry`. The unifying structural pattern is
--   a *duality of quantifier position*: soundness quantified over all valuations
--   (`UniformlySoundAt`) is equivalent to a self-loop and hence incompatible with
--   well-foundedness; soundness relative to one fixed valuation (`SoundAtV`) can be
--   named inside the language on a well-behaved frame (`namesSoundness_two_world`) —
--   weak internalisation is cheap, uniform internalisation is fatal.  What fails, and
--   why: attempts to derive reflexivity from `NamesSoundness` alone are hopeless
--   (the 2-world model is a counterexample: `f` is irreflexive and the naming still
--   holds), so the second-incompleteness punch needs the extra premise that the
--   system *asserts* its soundness predicate (`hglobal`), which is exactly the
--   informal reading of "the system proves its own soundness".
--
-- Critique (Critic):
--   No theorem is vacuous: `uniformlySoundAt_of_selfLoop` and
--   `soundnessExt_sound_none` exhibit inhabited instances of the sound-world notion,
--   and `namesSoundness_two_world` is a concrete finite model, so the impossibility
--   results are not about empty notions.  The equivalences use only one propositional
--   variable (`p : α` is an explicit hypothesis, not a rich-language assumption).
--   `sound_loeb_frame_isEmpty` and `glFrame_isEmpty_of_global_self_soundness` conclude
--   `IsEmpty`, which is a genuine refutation, not a vacuity artefact: the hypotheses
--   are shown satisfiable in isolation (Parts 3 and 5).  No proof is circular; each
--   result depends only on earlier ones.
--
-- Synthesis (PI):
--   Internal soundness, well-foundedness, and nonemptiness form an inconsistent triad;
--   dropping well-foundedness costs exactly one self-loop and nothing else (the
--   extension is conservative).  Next-cycle conjectures in `FUTURE_DIRECTIONS.md`.
-- !-- Lab Notes -- !--
open TangledSoundness in
theorem solution(F : KFrame) :
    (∀ X : Set F.W, boxOp F X ⊆ X → X = Set.univ) ↔
      WellFounded (Function.swap F.R) := by
  constructor
  · intro h
    have hacc := h {w | Acc (Function.swap F.R) w} (le_of_eq (boxOp_accSet F))
    refine ⟨fun w => ?_⟩
    have : w ∈ ({w | Acc (Function.swap F.R) w} : Set F.W) := by rw [hacc]; trivial
    exact this
  · intro hwf X hX
    ext w
    simp only [Set.mem_univ, iff_true]
    induction w using hwf.induction with
    | _ w ih => exact hX (fun v hv => ih v hv)
