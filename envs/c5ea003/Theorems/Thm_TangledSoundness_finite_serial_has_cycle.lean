-- Prove2me | Theorems.Thm_TangledSoundness_finite_serial_has_cycle
-- name    : TangledSoundness.finite_serial_has_cycle
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:48:02.834875+00:00
-- url     : https://prove2.me/theorems/ee035c06-26e1-4071-ac62-d0685aa08f28
-- title:
--   Finite + serial ⇒ cyclic.
-- statement:
--   **Finite + serial ⇒ cyclic.**  A finite frame in which every world has a successor
--   contains a world lying on a cycle.
--
--   ```lean
--   theorem TangledSoundness.finite_serial_has_cycle(F : KFrame) [Finite F.W] [Nonempty F.W]
--       (hser : ∀ w : F.W, ∃ v, F.R w v) : ∃ w : F.W, Relation.TransGen F.R w w := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/ProvabilityLogic/SelfConsistentSemantics.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/ProvabilityLogic/SelfConsistentSemantics.lean#L122

-- Thm stub generated from Logic/ProvabilityLogic/SelfConsistentSemantics.lean
import Mathlib
import Definitions.Def_Logic_ProvabilityLogic_SelfConsistentSemantics
import Definitions.Def_Logic_ProvabilityLogic_SelfSoundSystems
import Definitions.Def_Logic_ProvabilityLogic_TangledSoundness
/-
# Cycle 5: Every Finite Semantics of a Self-Consistent System Is Tangled

Cycle 4 built proof systems (`ModalSystem`) and showed that internal soundness and the
Löb axiom cannot coexist.  This cycle answers the remaining half of the mission
statement — *"tangled hierarchies are unavoidable in any system that can reason about
its own consistency"* — on the semantic side, and closes one step of the
`FUTURE_DIRECTIONS.md` degree-monoid conjecture.

## Main results

* `ModalSystem.serial_of_provesCon` — if a system proves its own consistency `¬□⊥`
  and a frame is sound for it, that frame is **serial**: no world is a dead end.
* `ModalSystem.isEmpty_of_provesCon_of_wf`, `glFrame_not_frameSound_of_provesCon` —
  hence no *nonempty* converse well-founded (GL) frame is sound for a system that
  asserts its own consistency.
* `finite_serial_has_cycle` and `ModalSystem.provesCon_finite_isTangled` —
  **the unavoidability theorem:** every *finite* frame sound for a system that proves
  its own consistency contains a cycle, so its reference graph (the transitive closure
  of accessibility) is tangled in the sense of `Logic.TangledHierarchies`.  Finiteness
  is the honest boundary: infinite serial frames such as `ω` with `n ↦ n+1` are
  loop-free, and that frame is exhibited (`omegaChain_serial_loopFree`) to show the
  hypothesis cannot be dropped.
* `iterSound_add`, `iterSound_zero` — the internal soundness degrees of a world form a
  submonoid of `(ℕ, +)`, the first step of conjecture C1.

## Relationship to catalog
Extends `Logic.ProvabilityLogic.SelfSoundSystems` (Cycle 4) and reuses `iterR`,
`transGen_of_iterR`, `sat_con_iff` from Cycle 3.
-/


open TangledSoundness

open GLPLogic

variable {α : Type}

/-! ## Part A — Degrees of internal soundness form a monoid -/




/-! ## Part B — Frame soundness and internal consistency -/





/-! ## Part C — Finite serial frames contain cycles -/

theorem TangledSoundness.finite_serial_has_cycle(F : KFrame) [Finite F.W] [Nonempty F.W]
    (hser : ∀ w : F.W, ∃ v, F.R w v) : ∃ w : F.W, Relation.TransGen F.R w w := by sorry
