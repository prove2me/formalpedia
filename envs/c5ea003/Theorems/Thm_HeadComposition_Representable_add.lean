-- Prove2me | Theorems.Thm_HeadComposition_Representable_add
-- name    : HeadComposition.Representable.add
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:36:40.485554+00:00
-- url     : https://prove2.me/theorems/fd01656d-9f76-43f9-86de-b0d7c20a4127
-- title:
--   Concatenating head sets.
-- statement:
--   **Concatenating head sets.**  A model for `f` with `H₁` heads and a model for `g` with `H₂`
--   heads combine into a model for `f + g` with `H₁ + H₂` heads.
--
--   ```lean
--   theorem HeadComposition.Representable.add{f g : X → Y → ℝ} {H₁ H₂ : ℕ}
--       (hf : Representable f H₁) (hg : Representable g H₂) :
--       Representable (fun x => f x + g x) (H₁ + H₂) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/TransformerUniversality/HeadComposition.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/TransformerUniversality/HeadComposition.lean#L115

-- Thm stub generated from MachineLearning/TransformerUniversality/HeadComposition.lean
import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_HeadComposition

/-!
# Compositional behaviour of head complexity

`Catalog/MachineLearning/TransformerUniversality/HeadComplexity.lean` characterizes the minimal
number of heads of a value-sum architecture computing a finite value table `f` as the rank of
that table.  The second next-cycle sub-conjecture of `FUTURE_DIRECTIONS.md` asked how this
resource behaves under composition.  This file settles it.

We repeat the definitions of that file (each catalog file is self-contained):
a *value-sum architecture with `H` heads* computes `model x = ∑ h : Fin H, c h x • v h`, with
arbitrary input-dependent scalar gates `c h` and input-independent value vectors `v h`.

Main results:

* `Representable.postcomp` / `minHeads_postcomp_le` — post-composition with a **linear**
  read-out never increases the head count;
* `minHeads_postcomp_of_injective` — and never decreases it either when the read-out is
  injective, because an injective linear map between vector spaces has a linear left inverse;
  hence head complexity is an invariant of the value table up to linear isomorphism;
* `minHeads_postcomp_zero` — the inequality really can be strict (the zero read-out), so
  injectivity is not a technical artifact;
* `Representable.add` / `minHeads_add_le` — **subadditivity**: heads of a sum of tasks are at
  most the sum of the heads, realized by concatenating the two head sets (`Fin.append`);
* `minHeads_smul_le`, `minHeads_precomp_le` — scaling the task and restricting the input
  domain do not increase head complexity;
* `minHeads_le_card` — the catalog's exact-lookup construction as an upper bound, which is
  also what makes `minHeads` a genuine minimum (the defining set is nonempty).

Together these say that `minHeads` is a *monotone, subadditive, linear-isomorphism invariant*
of the value table: exactly the formal properties one wants from a complexity measure, and the
properties needed to reason about stacked attention blocks rather than a single layer.
-/

open scoped BigOperators

open HeadComposition

variable {X X' Y Z : Type*} [Fintype X]













omit [Fintype X] in

theorem HeadComposition.Representable.add{f g : X → Y → ℝ} {H₁ H₂ : ℕ}
    (hf : Representable f H₁) (hg : Representable g H₂) :
    Representable (fun x => f x + g x) (H₁ + H₂) := by sorry
