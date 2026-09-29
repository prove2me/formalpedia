-- Prove2me | Theorems.Thm_TangledSoundness_namesSoundness_two_world
-- name    : TangledSoundness.namesSoundness_two_world
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:48:35.821423+00:00
-- url     : https://prove2.me/theorems/2e34fa9c-7b28-479f-96dc-2371c89ec930
-- title:
--   Existence of an internal soundness predicate.
-- statement:
--   **Existence of an internal soundness predicate.**  On `twoWorldTangle` the
--   valuation `V () := {t}` satisfies the fixed-point condition: the variable names
--   exactly the sound worlds — and it does so *non-vacuously*, since `t` is sound and `f`
--   is not.  So a proof system genuinely can contain a correct predicate for its own
--   soundness; what it cannot do (Part 1) is *validate* that predicate uniformly while
--   staying well-founded.
--
--   ```lean
--   theorem TangledSoundness.namesSoundness_two_world:
--       NamesSoundness twoWorldTangle (fun (_ : Unit) (w : Bool) => w = true) () := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/ProvabilityLogic/TangledSoundness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/ProvabilityLogic/TangledSoundness.lean#L381

-- Thm stub generated from Logic/ProvabilityLogic/TangledSoundness.lean
import Mathlib
import Definitions.Def_Logic_ProvabilityLogic_GLPFrames
import Definitions.Def_Logic_ProvabilityLogic_TangledSoundness
import Definitions.Def_Logic_TangledHierarchies
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

theorem TangledSoundness.namesSoundness_two_world:
    NamesSoundness twoWorldTangle (fun (_ : Unit) (w : Bool) => w = true) () := by sorry
