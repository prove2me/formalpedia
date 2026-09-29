-- Prove2me | Definitions.Def_MachineLearning_TransformerUniversality_HeadComplexity
-- name    : MachineLearning_TransformerUniversality_HeadComplexity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:16:27.424989+00:00
-- url     : https://prove2.me/theorems/569e1150-05c8-40b2-b91a-050dc2219f0b
-- title:
--   Aether Catalog definitions — MachineLearning_TransformerUniversality_HeadComplexity
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.TransformerUniversality.HeadComplexity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/TransformerUniversality/HeadComplexity.lean by skeleton subtraction
import Mathlib

/-!
# Exact head complexity of the attention lookup architecture

The catalog file `Catalog/MachineLearning/TransformerArchitecture.lean` realizes an arbitrary
function on a finite domain using **one head per possible input**, and explicitly flags the
resulting head count as a defect.  This file settles the question exactly.

A *value-sum architecture with `H` heads* computes
`model x = ∑ h : Fin H, c h x • v h`,
where the scalar gates `c h : X → ℝ` may be arbitrary (this is more general than attention:
softmax gates, bilinear gates, or any nonlinear gate are all special cases) and the `H` value
vectors `v h` are input-independent.  The catalog architecture is the special case
`c a x = ⟦x = a⟧`, `v a = f a`, with `H = |X|`.

Main results:

* `Representable.finrank_le` — a lower bound: any `H`-head model of `f` forces
  `finrank (span (range f)) ≤ H`;
* `representable_finrank` — a matching constructive upper bound: `finrank (span (range f))`
  heads always suffice;
* `minHeads_eq_finrank` — hence the minimal head count is *exactly* the rank of the value
  table, an exact resource characterization;
* `minHeads_eq_card_of_linearIndependent` — the catalog's `|X|` heads are necessary precisely
  when the value tables are linearly independent, and
* `minHeads_le_one_of_rank_one` — a family of tasks where a single head replaces `|X|` of
  them, so the exponential head count of exact finite lookup is an artifact of worst-case
  rank, not of the architecture.
-/

open scoped BigOperators
open Submodule Set Module

namespace HeadComplexity

variable {X Y : Type*} [Fintype X]

/-- A value-sum architecture with `H` heads: input-dependent scalar gates times
input-independent value vectors. -/
def Representable (f : X → Y → ℝ) (H : ℕ) : Prop :=
  ∃ (c : Fin H → X → ℝ) (v : Fin H → (Y → ℝ)), ∀ x, f x = ∑ h, c h x • v h

/-- The rank of the value table: the dimension of the span of all outputs. -/
noncomputable def rankOf (f : X → Y → ℝ) : ℕ := finrank ℝ (span ℝ (Set.range f))

instance finiteSpanRange (f : X → Y → ℝ) : Module.Finite ℝ (span ℝ (Set.range f)) :=
  Module.Finite.span_of_finite ℝ (Set.finite_range f)



/-- The minimal number of heads of a value-sum architecture computing `f`. -/
noncomputable def minHeads (f : X → Y → ℝ) : ℕ := sInf {H | Representable f H}






end HeadComplexity


