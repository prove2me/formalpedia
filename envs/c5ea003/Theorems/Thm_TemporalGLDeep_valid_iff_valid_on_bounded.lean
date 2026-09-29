-- Prove2me | Theorems.Thm_TemporalGLDeep_valid_iff_valid_on_bounded
-- name    : TemporalGLDeep.valid_iff_valid_on_bounded
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:55:40.94184+00:00
-- url     : https://prove2.me/theorems/951b09ab-bc51-4d5a-ad23-cd5873700258
-- title:
--   Validity is decided by bounded models.
-- statement:
--   **Validity is decided by bounded models.**  A formula is valid on all temporal GL
--   frames iff it is valid on all such frames with at most `2 ^ (2 * subformulaCount A)`
--   worlds.  This is exactly the statement that exhaustive bounded model search is a
--   *correct* (complete) semantic test — the search space is finite for each `A`.
--
--   ```lean
--   theorem TemporalGLDeep.valid_iff_valid_on_bounded(A : TForm) :
--       Valid A ↔ ∀ (N : TempModel) (v : N.F.W), Finite N.F.W →
--         Nat.card N.F.W ≤ 2 ^ (2 * subformulaCount A) → N.sat v A := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/PosetTheory/TemporalGLFiniteModel.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/PosetTheory/TemporalGLFiniteModel.lean#L326

-- Thm stub generated from Logic/PosetTheory/TemporalGLFiniteModel.lean
import Mathlib
import Definitions.Def_Logic_PosetTheory_TemporalGL
import Definitions.Def_Logic_PosetTheory_TemporalGLFiniteModel
import Definitions.Def_Logic_PosetTheory_TemporalGLSyntax

/-!
# Temporal Gödel–Löb logic: filtration and an explicit finite-model bound

This file proves the **small model property** for the temporal Gödel–Löb calculus TGL
of `TemporalGLSyntax.lean` over the catalog's frame class `TemporalGL.TempFrame`:

> if a formula `A` fails somewhere in *some* temporal GL model, then it already fails in
> a temporal GL model with at most `2 ^ (2 * subformulaCount A)` worlds.

The construction is a **filtration** through the subformulas of `A`, but a naive
filtration will not do: the quotient relation must simultaneously

* stay transitive (`TempFrame.R_trans`),
* stay **converse well-founded** (`TempFrame.R_wf`) — the Löb condition,
* keep the temporal order a preorder (`T_refl`, `T_trans`),
* and preserve the *interaction* condition `TempFrame.compat`
  (`T w w' → R w' v → R w v`), which is what validates the axiom `◻A ⟹ ◼◻A`.

The relation `filtR` below is the Segerberg-style GL filtration (successors must
*strictly increase* the set of realised boxes, which yields converse well-foundedness
from a counting argument), and `filtT` is its temporal companion, strengthened by a
`◻`-clause precisely so that `compat` survives filtration.  The strengthening is sound
because `compat` in the original model already forces `◻`-formulas to persist along `T`.

## Main results

* `filtR_measure_lt` — every `filtR`-step strictly increases the number of realised
  boxed subformulas; this is the combinatorial heart of converse well-foundedness.
* `filtFrame` — the filtered frame is a genuine `TemporalGL.TempFrame`.
* `truth_lemma` — the filtration lemma: on realised worlds the filtered model agrees
  with the original model on every subformula of `A`.
* `bounded_countermodel` — **main theorem**: any countermodel can be shrunk to one with
  at most `2 ^ subformulaCount A` (hence at most `2 ^ (2 * subformulaCount A)`) worlds.
* `finite_model_property_of_completeness` — the conjectured finite model property with
  the explicit bound `2 ^ (2 * subformulaCount A)`, for every non-derivable `A`, given
  weak completeness of TGL.
* `decidable_validity_reduces_to_bounded_check` — validity is equivalent to validity on
  models of size at most `2 ^ (2 * subformulaCount A)`, which is the statement that
  makes "exhaustive bounded model search" a correct decision procedure.
-/

open TemporalGLDeep

open TemporalGL

/-! ## 1. The filtration relations

Both relations are defined on arbitrary finite sets of formulas; `Cl` will always be
`subformulas A`. -/






/-! ## 2. The counting measure and converse well-foundedness -/







/-! ## 3. The filtered model -/

variable (M : TempModel) (A : TForm)








instance : DecidableEq (FWorld M A) := fun _ _ => decidable_of_iff _ Subtype.ext_iff.symm






/-! ## 4. The truth (filtration) lemma -/


/-! ## 5. The size bound -/


/-! ## 6. Main theorems -/

theorem TemporalGLDeep.valid_iff_valid_on_bounded(A : TForm) :
    Valid A ↔ ∀ (N : TempModel) (v : N.F.W), Finite N.F.W →
      Nat.card N.F.W ≤ 2 ^ (2 * subformulaCount A) → N.sat v A := by sorry
