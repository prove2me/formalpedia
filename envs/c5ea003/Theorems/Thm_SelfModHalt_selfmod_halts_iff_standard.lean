-- Prove2me | Theorems.Thm_SelfModHalt_selfmod_halts_iff_standard
-- name    : SelfModHalt.selfmod_halts_iff_standard
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:05:42.254864+00:00
-- url     : https://prove2.me/theorems/6cf9e933-d0c1-43c2-8b0f-67b46d3b975a
-- title:
--   Code is data.
-- statement:
--   **Code is data.**  A self-modifying machine halts exactly when its fixed-program
--   simulation halts.
--
--   ```lean
--   theorem SelfModHalt.selfmod_halts_iff_standard(m : SelfModMachine P S) (cfg : SelfModConfig P S) :
--       m.halts cfg ↔ m.toStd.halts (cfg.prog, cfg.state) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/SelfModHalt.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/SelfModHalt.lean#L95

-- Thm stub generated from Probability/SelfModHalt.lean
import Mathlib
import Definitions.Def_Probability_SelfModHalt

/-! # Self-modifying machines and their halting problem

This module supplies the machine model used by
`Novelty.SelfModifyingUndecidability`, whose own import of it was lost from the catalog
snapshot: a *self-modifying* machine carries its program inside the configuration and
may rewrite it at every step, whereas a *standard* machine has a fixed transition
function on a state space.

The main content is the simulation lemma `selfmod_halts_iff_standard` ("code is data"):
storing the changing program in the state turns a self-modifying machine into an
ordinary one with the *same* halting behaviour, so self-modification does not raise the
degree of the halting problem.
-/

open SelfModHalt







variable {P S X : Type*}

theorem SelfModHalt.selfmod_halts_iff_standard(m : SelfModMachine P S) (cfg : SelfModConfig P S) :
    m.halts cfg ↔ m.toStd.halts (cfg.prog, cfg.state) := by sorry
