-- Prove2me | Theorems.Thm_SelfModHalt_selfmod_halting_turing_equiv
-- name    : SelfModHalt.selfmod_halting_turing_equiv
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:05:52.883549+00:00
-- url     : https://prove2.me/theorems/8793e0ff-4774-4c12-a124-80bfcd2b307a
-- title:
--   Mutual reducibility.
-- statement:
--   **Mutual reducibility.**  Self-modifying halting and fixed-program halting are
--   many-one interreducible: the rewrite capability changes the operational presentation but
--   not the computability degree.
--
--   ```lean
--   theorem SelfModHalt.selfmod_halting_turing_equiv(m : SelfModMachine P S) :
--       ManyOneReduces m.halts m.toStd.halts ∧
--         ∃ m' : SelfModMachine Unit (P × S), ManyOneReduces m.toStd.halts m'.halts := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/SelfModHalt.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/SelfModHalt.lean#L142

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

theorem SelfModHalt.selfmod_halting_turing_equiv(m : SelfModMachine P S) :
    ManyOneReduces m.halts m.toStd.halts ∧
      ∃ m' : SelfModMachine Unit (P × S), ManyOneReduces m.toStd.halts m'.halts := by sorry
