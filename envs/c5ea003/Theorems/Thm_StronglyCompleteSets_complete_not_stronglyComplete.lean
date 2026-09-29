-- Prove2me | Theorems.Thm_StronglyCompleteSets_complete_not_stronglyComplete
-- name    : StronglyCompleteSets.complete_not_stronglyComplete
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:45:32.733594+00:00
-- url     : https://prove2.me/theorems/ed951cf6-5925-4a57-94ee-83d43d22271e
-- title:
--   Counterexample to a tempting conjecture: completeness does not imply strong
-- statement:
--   **Counterexample to a tempting conjecture:** completeness does not imply strong
--   completeness.  Deleting `1` from `evenWithOne` leaves only even summands.
--
--   ```lean
--   theorem StronglyCompleteSets.complete_not_stronglyComplete:
--       Complete evenWithOne ∧ ¬ StronglyComplete evenWithOne := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/StronglyCompleteSets/Contrarian.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/StronglyCompleteSets/Contrarian.lean#L133

-- Thm stub generated from Logic/StronglyCompleteSets/Contrarian.lean
import Mathlib
import Definitions.Def_Logic_StronglyCompleteSets_Contrarian

/-!
# Strongly complete sets: structural results and a counterexample

This file formalizes the basic notions from *Strongly complete sets and a conjecture
of Erdős*.  It then tests the tempting strengthening “every complete set is strongly
complete”.  The statement is false: the set consisting of all even natural numbers
together with `1` is complete, but deleting `1` leaves a parity obstruction.

We also prove that strong completeness is unchanged by a finite perturbation.  This
isolates the robustness built into the paper's definition.
-/

open StronglyCompleteSets

theorem StronglyCompleteSets.complete_not_stronglyComplete:
    Complete evenWithOne ∧ ¬ StronglyComplete evenWithOne := by sorry
