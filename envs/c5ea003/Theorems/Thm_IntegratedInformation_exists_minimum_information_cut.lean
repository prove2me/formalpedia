-- Prove2me | Theorems.Thm_IntegratedInformation_exists_minimum_information_cut
-- name    : IntegratedInformation.exists_minimum_information_cut
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:59:06.823612+00:00
-- url     : https://prove2.me/theorems/e4b28e93-3770-404b-af00-2609e006dc69
-- title:
--   Some admissible cut realizes the integrated information.
-- statement:
--   Some admissible cut realizes the integrated information.
--
--   ```lean
--   theorem IntegratedInformation.exists_minimum_information_cut(S : CausalStructure) :
--       ∃ c : S.Cut, S.loss c = Phi S := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/IntegratedInformation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/IntegratedInformation.lean#L32

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

theorem IntegratedInformation.exists_minimum_information_cut(S : CausalStructure) :
    ∃ c : S.Cut, S.loss c = Phi S := by sorry
