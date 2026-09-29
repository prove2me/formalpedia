-- Prove2me | Definitions.Def_MachineLearning_TropicalRobustness
-- name    : MachineLearning_TropicalRobustness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:17:25.008373+00:00
-- url     : https://prove2.me/theorems/be7895d7-24ce-43e7-b513-808d387a653a
-- title:
--   Aether Catalog definitions — MachineLearning_TropicalRobustness
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.TropicalRobustness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/TropicalRobustness.lean by skeleton subtraction
import Mathlib

/-!
# Tropical Certified Robustness for Hierarchical Max-Aggregation Trees

We formalize certified robustness guarantees for multiclass piecewise-linear
networks with hierarchical max-aggregation. The key results establish that
**pairwise multiclass margins admit a recursive subtree certificate**: a local
tropical comparison margin at every internal node propagates monotonically to
the root, and the only global penalty is the accumulated max-Lipschitz constant.

## Main definitions

* `AggTree`: Binary aggregation tree with pointwise-max at internal nodes.
* `AggTree.eval`: Recursive evaluation yielding class scores.
* `AggTree.lip`: Recursive Lipschitz bound (max across leaves).
* `AggTree.certGap`: Recursive certified gap (min of subtree logit gaps).
* `AggTree.IsStrictWinner`: Predicate for strict argmax classification.
* `AggTree.certRadius`: Certified robustness radius.

## Main results

* `AggTree.eval_lip`: Tree evaluation is Lipschitz with constant `lip`.
* `AggTree.certGap_le_gap`: Certified gap lower-bounds the actual gap.
* `AggTree.gap_perturb_lower_bound`: Gap degrades by ≤ 2·L·dist under perturbation.
* `AggTree.argmax_stable`: Classification stability under perturbation.
* `AggTree.certRadius_spec`: Robustness within the certified radius.

## References

The tropical approach to certified robustness originates in the analysis of
ReLU networks as tropical rational maps. This formalization extends flat
max-pooling certificates to genuinely deep hierarchical max architectures.
-/

namespace TropicalRobustness

/-- A binary aggregation tree for hierarchical max-pooling over class scores.
Leaves carry class-score function families `κ → α → ℝ` and a Lipschitz constant `L`.
Internal nodes aggregate two subtrees by taking the pointwise maximum of scores.
Any finite-arity aggregation tree can be encoded as a binary tree. -/
inductive AggTree (κ : Type*) (α : Type*) where
  /-- A leaf node carrying a score function family and its Lipschitz constant. -/
  | leaf (f : κ → α → ℝ) (L : ℝ)
  /-- A binary internal node taking pointwise max of two subtrees. -/
  | bin (left right : AggTree κ α)

variable {κ α : Type*} [PseudoMetricSpace α]

namespace AggTree

/-- Recursive evaluation of the aggregation tree. At leaves, evaluate the
stored score function. At binary nodes, take the pointwise maximum of children. -/
def eval : AggTree κ α → α → κ → ℝ
  | .leaf f _, x, i => f i x
  | .bin l r, x, i => max (l.eval x i) (r.eval x i)

/-- Recursive Lipschitz bound: maximum Lipschitz constant across all leaves in the tree. -/
def lip : AggTree κ α → ℝ
  | .leaf _ L => L
  | .bin l r => max l.lip r.lip

/-- Validity predicate: each leaf's score functions are actually Lipschitz
with their stored constant. -/
def IsValid : AggTree κ α → Prop
  | .leaf f L => ∀ i : κ, ∀ x y : α, |f i x - f i y| ≤ L * dist x y
  | .bin l r => l.IsValid ∧ r.IsValid

/-- The logit gap (score difference) between classes `i` and `j` at input `x`. -/
def gap (T : AggTree κ α) (x : α) (i j : κ) : ℝ :=
  T.eval x i - T.eval x j

/-- Recursive certified gap: at leaves, the actual score gap; at internal nodes,
the minimum over children's certified gaps. This is a lower bound on the true
logit gap at the root, justified by the tropical monotonicity property that
selecting the child maximizing a class score witnesses the gap inequality. -/
def certGap : AggTree κ α → α → κ → κ → ℝ
  | .leaf f _, x, i, j => f i x - f j x
  | .bin l r, x, i, j => min (l.certGap x i j) (r.certGap x i j)

/-- A class `y` is the strict winner at input `x` if it has strictly higher
score than every other class. -/
def IsStrictWinner (T : AggTree κ α) (x : α) (y : κ) : Prop :=
  ∀ j, j ≠ y → T.eval x y > T.eval x j

/-! ### Real analysis lemmas for binary max -/

/-
The difference `max a b - max c d` is at most `max (a - c) (b - d)`.
This is the one-sided binary-max Lipschitz estimate.
-/

/-
The absolute difference of binary maxima is bounded by the max of
absolute differences. This is the symmetric binary-max Lipschitz estimate,
the fundamental building block for inductive Lipschitz propagation.
-/

/-
The minimum of pairwise differences lower-bounds the difference of maxima.
This is the key tropical monotonicity inequality: choosing the child that
maximizes the "denominator" class shows the parent gap is at least as large.
-/

/-
An algebraic perturbation estimate: if `|a - a'| ≤ L * δ` and
`|b - b'| ≤ L * δ`, then `a' - b' ≥ (a - b) - 2 * L * δ`.
-/

/-! ### Tree evaluation is Lipschitz -/

/-
**Max-preserves-Lipschitz theorem.** If each leaf is Lipschitz with its
stored constant, then the entire tree evaluation is Lipschitz with the
global maximum constant `lip T`. Proved by structural induction using the
binary-max Lipschitz estimate `abs_max_sub_max_le`.
-/

/-! ### Certified gap lower bounds the actual gap -/

/-
**Subtree certificate monotonicity.** The recursive certified gap is a
lower bound on the actual logit gap. At leaves this is an equality. At internal
nodes, the minimum child certificate is ≤ the parent gap because picking the
child that maximizes the losing class shows the parent gap exceeds that child's
gap.
-/

/-! ### Gap perturbation bound -/

/-
**Gap degradation bound.** Under input perturbation from `x` to `y`,
pairwise logit gaps degrade by at most `2 * lip T * dist x y`. This follows
from the triangle inequality applied separately to each class score.
-/

/-! ### Classification stability -/

/-
**Argmax stability theorem.** If the certified gap between the winning
class `c` and every competitor exceeds twice the Lipschitz constant times the
perturbation distance, then `c` remains the strict winner at the perturbed
input. This combines the subtree certificate monotonicity with the gap
degradation bound.
-/

/-! ### Certified robustness radius -/

/-- The certified robustness radius: the minimum over competing classes of
the certified gap divided by twice the Lipschitz constant.
When there is only one class, the radius is defined to be zero (the stability
conclusion holds vacuously in that case). -/
noncomputable def certRadius [Fintype κ] [DecidableEq κ]
    (T : AggTree κ α) (x : α) (c : κ) : ℝ :=
  if h : (Finset.univ.erase c).Nonempty then
    (Finset.univ.erase c).inf' h (fun j => T.certGap x c j / (2 * T.lip))
  else 0

/-
**Certified robustness radius theorem.** If every pairwise certified gap
is positive and the input perturbation is within the certified radius, then
the predicted class remains the strict winner. This is the main robustness
guarantee, giving a compositional, formally verified certificate for
tree-structured piecewise-linear networks.
-/

end AggTree

end TropicalRobustness


