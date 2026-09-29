-- Prove2me | Theorems.Thm_TangledSoundness_transGen_iterate
-- name    : TangledSoundness.transGen_iterate
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:47:52.446029+00:00
-- url     : https://prove2.me/theorems/0be77810-aac4-4d2b-8f7d-fba77705d92f
-- title:
--   Iterating a successor-choice function follows accessibility.
-- statement:
--   Iterating a successor-choice function follows accessibility.
--
--   ```lean
--   theorem TangledSoundness.transGen_iterate{F : KFrame} {f : F.W → F.W} (hf : ∀ x, F.R x (f x))
--       (w : F.W) : ∀ (i k : ℕ), 0 < k → Relation.TransGen F.R (f^[i] w) (f^[i + k] w) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/ProvabilityLogic/SelfConsistentSemantics.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/ProvabilityLogic/SelfConsistentSemantics.lean#L103

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

theorem TangledSoundness.transGen_iterate{F : KFrame} {f : F.W → F.W} (hf : ∀ x, F.R x (f x))
    (w : F.W) : ∀ (i k : ℕ), 0 < k → Relation.TransGen F.R (f^[i] w) (f^[i + k] w) := by sorry
