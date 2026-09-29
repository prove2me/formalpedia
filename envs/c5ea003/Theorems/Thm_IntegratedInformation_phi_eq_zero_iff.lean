-- Prove2me | Theorems.Thm_IntegratedInformation_phi_eq_zero_iff
-- name    : IntegratedInformation.phi_eq_zero_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:03:18.051327+00:00
-- url     : https://prove2.me/theorems/f80c7be1-dfdb-4139-a221-1b747d2350b2
-- title:
--   A causal structure is reducible exactly when one admissible cut destroys no
-- statement:
--   A causal structure is reducible exactly when one admissible cut destroys no
--   causal information.
--
--   ```lean
--   theorem IntegratedInformation.phi_eq_zero_iff(S : CausalStructure) :
--       Phi S = 0 ↔ ∃ c : S.Cut, S.loss c = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/IntegratedInformation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/IntegratedInformation.lean#L55

-- Thm stub generated from Novelty/IntegratedInformation.lean
import Mathlib
import Definitions.Def_Novelty_IntegratedInformation

/-! # Consciousness as Integrated Information

This file develops a finite mathematical model of integrated information.  A
causal structure has finitely many admissible cuts and a nonnegative loss at
each cut.  Its integrated information `Φ` is the least such loss.  Parallel
composition adds losses, while exclusion selects a maximally integrated member
of a finite family.  Pointwise comparison of loss functions supplies a small
category-like refinement calculus.
-/

open Finset

open IntegratedInformation


attribute [instance] CausalStructure.finiteCut CausalStructure.cutNonempty

theorem IntegratedInformation.phi_eq_zero_iff(S : CausalStructure) :
    Phi S = 0 ↔ ∃ c : S.Cut, S.loss c = 0 := by sorry
