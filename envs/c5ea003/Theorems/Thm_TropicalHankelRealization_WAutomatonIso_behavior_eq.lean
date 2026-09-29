-- Prove2me | Theorems.Thm_TropicalHankelRealization_WAutomatonIso_behavior_eq
-- name    : TropicalHankelRealization.WAutomatonIso.behavior_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:21:17.719165+00:00
-- url     : https://prove2.me/theorems/a771c19a-cefc-4cb4-a3dc-a9409f168ba1
-- title:
--   Behavior eq
-- statement:
--   Formal statement of `TropicalHankelRealization.WAutomatonIso.behavior_eq` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem TropicalHankelRealization.WAutomatonIso.behavior_eq{T₁ : WAutomaton K A n} {T₂ : WAutomaton K A m}
--       (iso : WAutomatonIso T₁ T₂) : T₁.behavior = T₂.behavior := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TropicalHankelRealizationDuality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TropicalHankelRealizationDuality.lean#L290

-- Thm stub generated from Bridges/TropicalHankelRealizationDuality.lean
import Mathlib
import Definitions.Def_Bridges_TropicalHankelRealizationDuality
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Hankel Realization Duality

A min-plus weighted analogue of the Schützenberger–Hankel theorem establishing that
**recognizability, finite residual generation, finite tropical Hankel rank, and
certified minimal realization all coincide** for weighted languages over commutative
semirings (with particular application to tropical/idempotent semirings).

## Main Results

* `recognizable_iff_fg_hankel_row` — Recognizability ↔ finitely generated Hankel rows
  with shift stability (the Schützenberger–Fliess realization theorem).
* `recognizable_implies_fg_residual` — Recognizability implies finitely generated residuals.
* `recognizable_implies_finite_hankel_rank` — Recognizability implies finite Hankel rank.
* `certified_reconstruction` — From a Hankel window certificate, reconstruct an automaton.
* `obs_matching_of_same_behavior` — Observable automata with matched observations
  produce an isomorphism.

## Mathematical Context

This formalizes the tropical analogue of the Schützenberger–Fliess–Carlyle–Paz
realization theorem. The correct invariant for recognizability is **finite generation
of the Hankel row semimodule** together with shift stability.

## Keywords

tropical automata, min-plus semiring, Hankel realization, Schützenberger theorem,
weighted languages, residual semimodule, tropical factor rank, automata minimization,
certified reconstruction, canonical realization
-/

open Finset BigOperators

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

open TropicalHankelRealization

/-! ## §1. Core Definitions -/


variable {K : Type*} [CommSemiring K]
variable {A : Type*} [DecidableEq A] [Fintype A]
variable {n m : ℕ}





def WAutomaton.stateCount (_ : WAutomaton K A n) : ℕ := n

/-! ## §2. Residuals and Hankel -/






/-! ## §3. Recognizability and Finite Generation -/






/-! ## §4. Forward Realization: Data → Automaton -/





/-! ## §5. Backward Direction: Automaton → Data -/






/-! ## §6. Realization Duality -/


/-! ## §7. Recognizable ↔ FGHankelRowSemimodule -/





/-! ## §8. Hankel Factor Rank -/



/-! ## §9. Automaton Isomorphism -/







omit [DecidableEq A] [Fintype A] in

theorem TropicalHankelRealization.WAutomatonIso.behavior_eq{T₁ : WAutomaton K A n} {T₂ : WAutomaton K A m}
    (iso : WAutomatonIso T₁ T₂) : T₁.behavior = T₂.behavior := by sorry
