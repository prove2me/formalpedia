-- Prove2me | Theorems.Thm_Logic_DPCompleteness_DPSpec_val_const_step
-- name    : Logic.DPCompleteness.DPSpec.val_const_step
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:27:28.073019+00:00
-- url     : https://prove2.me/theorems/198bfb3f-b7b9-45ca-b350-58b9edf5d38b
-- title:
--   If every transition carries the same weight `c`, the value function is
-- statement:
--   If every transition carries the same weight `c`, the value function is
--   `sup init + (n+1) • c` from stage `1` on.
--
--   ```lean
--   theorem Logic.DPCompleteness.DPSpec.val_const_step(D : DPSpec S W) (c : W) (h : ∀ i s t, D.step i s t = c) :
--       ∀ (n : ℕ) (t : S),
--         D.val (n + 1) t =
--           (Finset.univ : Finset S).sup' Finset.univ_nonempty D.init + (n + 1) • c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/DPCompletenessApplications.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/DPCompletenessApplications.lean#L65

-- Thm stub generated from Logic/DPCompletenessApplications.lean
import Mathlib
import Definitions.Def_Logic_DPCompleteness
import Definitions.Def_Logic_DPCompletenessApplications
import Definitions.Def_Logic_DPCompletenessWalks
/-
# Applications and specialisations of the DP completeness theorem

Building on `Logic.DPCompleteness` and `Logic.DPCompletenessWalks` this file records three
consequences of the general theory.

1. **Order duality (min-plus / shortest paths).**  Replacing the weight order by its dual turns
   the "greatest score" completeness theorem into a *minimality* theorem: every labelling
   *dominates* some dual DP run.  This is the Bellman–Ford shortest-path statement, obtained
   for free from the max-plus one.
2. **Closed form for stage-independent weights.**  When all transitions carry the same weight
   `c`, the value function collapses to `sup init + n • c`.
3. **A fully explicit three-state integer instance**, where the abstract value function is
   checked, inside Lean's kernel, against a brute-force enumeration of *all* labellings.
   This is a machine-checked instance of the completeness/exactness theorem.
-/


open Logic.DPCompleteness

open DPSpec

/-! ## Order duality: minimising runs -/


variable {S W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S] [LinearOrder W]
  [IsOrderedCancelAddMonoid W]







/-! ## Stage-independent weights -/


variable {S W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S] [LinearOrder W] [AddLeftMono W]

theorem Logic.DPCompleteness.DPSpec.val_const_step(D : DPSpec S W) (c : W) (h : ∀ i s t, D.step i s t = c) :
    ∀ (n : ℕ) (t : S),
      D.val (n + 1) t =
        (Finset.univ : Finset S).sup' Finset.univ_nonempty D.init + (n + 1) • c := by sorry
