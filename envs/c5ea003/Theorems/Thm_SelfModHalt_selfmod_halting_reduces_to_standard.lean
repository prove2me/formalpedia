-- Prove2me | Theorems.Thm_SelfModHalt_selfmod_halting_reduces_to_standard
-- name    : SelfModHalt.selfmod_halting_reduces_to_standard
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:05:55.690785+00:00
-- url     : https://prove2.me/theorems/b61732ed-90b3-40af-b974-e844fc23599d
-- title:
--   The halting problem of a self-modifying machine reduces to that of its
-- statement:
--   The halting problem of a self-modifying machine reduces to that of its
--   fixed-program simulation.
--
--   ```lean
--   theorem SelfModHalt.selfmod_halting_reduces_to_standard(m : SelfModMachine P S) :
--       ManyOneReduces m.halts m.toStd.halts := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/SelfModHalt.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/SelfModHalt.lean#L109

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

theorem SelfModHalt.selfmod_halting_reduces_to_standard(m : SelfModMachine P S) :
    ManyOneReduces m.halts m.toStd.halts := by sorry
