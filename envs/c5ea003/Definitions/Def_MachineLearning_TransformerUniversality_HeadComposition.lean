-- Prove2me | Definitions.Def_MachineLearning_TransformerUniversality_HeadComposition
-- name    : MachineLearning_TransformerUniversality_HeadComposition
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:17:03.942854+00:00
-- url     : https://prove2.me/theorems/fe5a1928-7871-4c25-be79-da9d7eff3e08
-- title:
--   Aether Catalog definitions — MachineLearning_TransformerUniversality_HeadComposition
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.TransformerUniversality.HeadComposition`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/TransformerUniversality/HeadComposition.lean by skeleton subtraction
import Mathlib

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

namespace HeadComposition

variable {X X' Y Z : Type*} [Fintype X]

/-- A value-sum architecture with `H` heads (cf. `HeadComplexity.Representable`). -/
def Representable (f : X → Y → ℝ) (H : ℕ) : Prop :=
  ∃ (c : Fin H → X → ℝ) (v : Fin H → (Y → ℝ)), ∀ x, f x = ∑ h, c h x • v h

/-- The minimal number of heads of a value-sum architecture computing `f`. -/
noncomputable def minHeads (f : X → Y → ℝ) : ℕ := sInf {H | Representable f H}




section PostComposition





end PostComposition

section Additivity





end Additivity


end HeadComposition


