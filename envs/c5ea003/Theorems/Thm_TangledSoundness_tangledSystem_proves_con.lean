-- Prove2me | Theorems.Thm_TangledSoundness_tangledSystem_proves_con
-- name    : TangledSoundness.tangledSystem_proves_con
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:53:57.008982+00:00
-- url     : https://prove2.me/theorems/1c8674ed-08d6-493a-a13d-e90eef5bbcf8
-- title:
--   The tangled system even proves its own consistency statement `¬□⊥` — precisely
-- statement:
--   The tangled system even proves its own consistency statement `¬□⊥` — precisely
--   what Gödel's second theorem denies to Löbian systems.
--
--   ```lean
--   theorem TangledSoundness.tangledSystem_proves_con:
--       (tangledSystem α).Thm (MFormula.con (α := α)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/ProvabilityLogic/SelfSoundSystems.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/ProvabilityLogic/SelfSoundSystems.lean#L190

-- Thm stub generated from Logic/ProvabilityLogic/SelfSoundSystems.lean
import Mathlib
import Definitions.Def_Logic_ProvabilityLogic_GLPFrames
import Definitions.Def_Logic_ProvabilityLogic_IteratedReflection
import Definitions.Def_Logic_ProvabilityLogic_SelfSoundSystems
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


open TangledSoundness

open GLPLogic

variable {α : Type}

/-! ## Part A — Abstract modal proof systems -/


open ModalSystem

variable (S : ModalSystem α)










/-! ## Part B — A consistent Löbian system: validity on GL frames -/







/-! ## Part C — A consistent system that *does* contain its own soundness predicate -/

theorem TangledSoundness.tangledSystem_proves_con:
    (tangledSystem α).Thm (MFormula.con (α := α)) := by sorry
