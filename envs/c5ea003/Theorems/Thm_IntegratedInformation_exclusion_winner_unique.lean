-- Prove2me | Theorems.Thm_IntegratedInformation_exclusion_winner_unique
-- name    : IntegratedInformation.exclusion_winner_unique
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:03:30.041055+00:00
-- url     : https://prove2.me/theorems/9f6352a4-bd5f-42b2-8d06-42b078948417
-- title:
--   If one candidate strictly exceeds all others, exclusion selects it
-- statement:
--   If one candidate strictly exceeds all others, exclusion selects it
--   uniquely.
--
--   ```lean
--   theorem IntegratedInformation.exclusion_winner_unique{ι : Type} [Fintype ι] [Nonempty ι]
--       (F : CandidateFamily ι) (winner : ι)
--       (h : ∀ i, i ≠ winner → Phi (F.system i) < Phi (F.system winner)) :
--       ∀ i, Phi (F.system i) = BigPhi F → i = winner := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/IntegratedInformation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/IntegratedInformation.lean#L155

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

theorem IntegratedInformation.exclusion_winner_unique{ι : Type} [Fintype ι] [Nonempty ι]
    (F : CandidateFamily ι) (winner : ι)
    (h : ∀ i, i ≠ winner → Phi (F.system i) < Phi (F.system winner)) :
    ∀ i, Phi (F.system i) = BigPhi F → i = winner := by sorry
