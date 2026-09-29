-- Prove2me | Definitions.Def_Logic_ProvabilityLogic_SelfSoundSystems
-- name    : Logic_ProvabilityLogic_SelfSoundSystems
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:06:20.941134+00:00
-- url     : https://prove2.me/theorems/f31f4a08-004b-403d-94de-0d5a2d5be04e
-- title:
--   Aether Catalog definitions — Logic_ProvabilityLogic_SelfSoundSystems
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.ProvabilityLogic.SelfSoundSystems`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/ProvabilityLogic/SelfSoundSystems.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_ProvabilityLogic_GLPFrames
import Definitions.Def_Logic_ProvabilityLogic_IteratedReflection
import Definitions.Def_Logic_ProvabilityLogic_TangledSoundness
/-
# Cycle 4: A Proof System That Contains Its Own Soundness Predicate

Cycles 1–3 worked on the semantic side (Kripke frames).  This cycle builds the
**syntactic** object the mission asks for: a formal proof system in whose language the
soundness predicate lives, together with two concrete, *consistent* systems on either
side of the divide and a proof that their union collapses.

A `ModalSystem` is a set of theorems over `GLPLogic.MFormula`, closed under modus
ponens and necessitation.  Inside such a system:

* the **soundness predicate** of the system is the reflection schema
  `□φ → φ` — "whatever this system proves is true" — written in the system's own
  language;
* the **Löb axiom** `□(□φ → φ) → □φ` is the syntactic trace of a well-founded
  provability hierarchy.

## Main results

* `ModalSystem.loeb_rule` — Löb's rule derived from the Löb axiom, necessitation and
  modus ponens: a system that proves an instance of its own soundness proves the
  instance itself.
* `ModalSystem.not_consistent_of_reflection_loeb` — **the tangle is unavoidable:** a
  Löbian system that contains its own soundness schema is inconsistent.
* `ModalSystem.not_provable_con_of_loeb` — Gödel's second incompleteness theorem in
  this setting: a consistent Löbian system cannot prove its own consistency `¬□⊥`.
* `glValiditySystem` — a **concrete consistent Löbian system** (validity on all GL
  frames), which therefore does *not* contain its own soundness predicate
  (`glValiditySystem_not_provesReflection`).
* `tangledSystem` — a **concrete consistent system that does contain its own soundness
  predicate** (truth at the single reflexive world), which therefore refutes the Löb
  axiom (`tangledSystem_not_provesLoebAxiom`), and whose world is `UniformlySoundAt`
  in the sense of Cycle 1 (`loopFrame_uniformlySound`).
* `soundness_loeb_trichotomy` — the capstone: soundness-internalisation and Löb are
  each separately consistent, and jointly inconsistent.  A hierarchy that reasons
  about its own consistency must be tangled, and a tangled one exists.

## Relationship to catalog
Uses `GLPLogic.MFormula`, `GLFrame`, `forces`, `loeb_valid` from
`Logic.ProvabilityLogic.GLPFrames` and the semantic apparatus of
`Logic.ProvabilityLogic.TangledSoundness` (Cycle 1).
-/


namespace TangledSoundness

open GLPLogic

variable {α : Type}

/-! ## Part A — Abstract modal proof systems -/

/-- A **modal proof system**: a set of theorems closed under modus ponens and
necessitation.  Nothing else is assumed, so every result below isolates exactly which
principles cause the collapse. -/
structure ModalSystem (α : Type) where
  /-- The theorems of the system. -/
  Thm : MFormula α → Prop
  /-- Modus ponens. -/
  mp : ∀ {φ ψ : MFormula α}, Thm (.imp φ ψ) → Thm φ → Thm ψ
  /-- Necessitation. -/
  nec : ∀ {φ : MFormula α}, Thm φ → Thm (.box φ)

namespace ModalSystem

variable (S : ModalSystem α)

/-- The system is **consistent** if it does not prove `⊥`. -/
def Consistent : Prop := ¬ S.Thm .bot

/-- The system **proves the Löb axiom** for every formula. -/
def ProvesLoebAxiom : Prop := ∀ φ : MFormula α, S.Thm (loebInst φ)

/-- The system **contains its own soundness predicate**: it proves every instance of
the reflection schema `□φ → φ`. -/
def ProvesReflection : Prop := ∀ φ : MFormula α, S.Thm (reflection φ)






end ModalSystem

/-! ## Part B — A consistent Löbian system: validity on GL frames -/

/-- The one-point GL frame: a single world with no accessible worlds. -/
def pointFrame : GLFrame where
  W := Unit
  R := fun _ _ => False
  R_trans := fun h _ => h.elim
  R_wf := ⟨fun a => ⟨a, fun _ h => h.elim⟩⟩

/-- **The GL validity system**: theorems are the formulas true at every world of every
GL (transitive, converse well-founded) frame under every valuation.  This is a genuine
proof system in the sense above. -/
def glValiditySystem (α : Type) : ModalSystem α where
  Thm φ := ∀ (M : GLFrame.{0}) (V : α → M.W → Prop) (w : M.W), forces M V w φ
  mp := fun h₁ h₂ M V w => h₁ M V w (h₂ M V w)
  nec := fun h M V _ v _ => h M V v





/-! ## Part C — A consistent system that *does* contain its own soundness predicate -/

/-- The one-point **tangled** frame: a single world accessing itself. -/
def loopFrame : KFrame where
  W := Unit
  R := fun _ _ => True


/-- **The tangled system**: theorems are the formulas true at the self-accessing world
under every valuation.  Its soundness predicate is *inside* it. -/
def tangledSystem (α : Type) : ModalSystem α where
  Thm φ := ∀ (V : α → loopFrame.W → Prop) (w : loopFrame.W), sat loopFrame V w φ
  mp := fun h₁ h₂ V w => h₁ V w (h₂ V w)
  nec := fun h V _ v _ => h V v





/-! ## Part D — Capstone: the trichotomy -/


end TangledSoundness

-- !-- Lab Notes -- !--
--
-- Hypothesis (Hypothesizer):
--   H14. Löb's *rule* ("if the system proves an instance of its own soundness it
--        proves the instance") is derivable from modus ponens, necessitation and the
--        Löb axiom alone — no propositional axioms needed.
--   H15. (Bold) The three properties "consistent", "proves reflection", "proves the
--        Löb axiom" are pairwise satisfiable but not jointly satisfiable, and both
--        pairwise witnesses can be built as concrete Kripke-validity systems.
--
-- Experiment (Experimenter):
--   H14: `ModalSystem.loeb_rule` is the three-step term
--        `S.mp h (S.mp (hL φ) (S.nec h))`; it needed no propositional-tautology
--        axioms, which is why `ModalSystem` has only two closure rules.
--   H15: `glValiditySystem` (validity on all GL frames) is Löbian by the catalog's
--        `loeb_valid` and consistent by evaluation at `pointFrame`; `tangledSystem`
--        (truth at the single reflexive world) proves reflection by
--        `hbox w trivial` and is consistent by evaluating at the empty valuation.
--        The impossibility half is `not_consistent_of_reflection_loeb`, whose only
--        content is Löb's rule applied to `φ = ⊥` (`reflection ⊥` is literally the
--        consistency formula `MFormula.con`).
--
-- Analysis (Analyst):
--   Survived: H14, H15, sorry-free.  What the experiment clarifies is *where* the
--   Gödelian obstruction lives: not in the arithmetic, not in the propositional base,
--   but in the interaction of necessitation with the Löb axiom.  Removing
--   necessitation (as a "local truth at the top world" system would) or removing Löb
--   (as `tangledSystem` does) both restore consistency with internal soundness; the
--   semantic counterpart in Cycle 1 is exactly `uniformlySound_iff_selfLoop` versus
--   `loebAt_irrefl`.
--
-- Critique (Critic):
--   Neither witness system is vacuous or trivially defined: `glValiditySystem` proves
--   nonempty theorem sets (every GL-valid formula, e.g. all Löb instances) and refutes
--   `⊥`, while `tangledSystem` proves all reflection instances and refutes `⊥`; both
--   consistency proofs evaluate at an explicit world of an explicit frame.  The
--   `ModalSystem` structure assumes only closure rules, so no hidden axiom is doing
--   the work.  No proof in this file references itself, and the capstone only
--   assembles earlier results.
-- !-- Lab Notes -- !--


