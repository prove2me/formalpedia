-- Prove2me | Definitions.Def_Novelty_AgreementSubtreesCounting
-- name    : Novelty_AgreementSubtreesCounting
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:01:58.394202+00:00
-- url     : https://prove2.me/theorems/624acbba-3b4b-4e8a-9961-cbb200123acb
-- title:
--   Aether Catalog definitions — Novelty_AgreementSubtreesCounting
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.AgreementSubtreesCounting`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/AgreementSubtreesCounting.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_AgreementSubtreesMultiple
import Definitions.Def_Novelty_Core

/-!
# Counting restrictions and the tower behind multiple-tree agreement subtrees

Snir and Yuster asked for the least number `h(k)` of leaves that force `k` unrooted binary
phylogenetic trees to share a common quartet.  The upper-bound arguments for the many-tree
Maximum Agreement Subtree problem are driven by two elementary but decisive facts:

* the induced split system of a tree on `a` retained leaves is one of at most `2^(2^a)`
  possibilities (a *double* exponential), because every such system is a set of subsets of
  the `a` leaves; and
* once the number of trees exceeds this count, two trees must induce *identical* systems on
  the retained leaves — a pigeonhole step that seeds the iterated-exponential recursion.

This chapter isolates these facts from the analytic bookkeeping, and develops the
arithmetic of the iterated exponential *tower* `iterExp n a = 2^(2^(⋯^a))` in which the
paper's four-times iterated exponential bound lives (`iterExp 4`).

The results build directly on the restriction algebra of `Catalog.Applications.Core`
(`restrict`, `AgreeOn`, `CommonAgreement`).

-- !-- Lab Notes -- !--
## Hypothesis (Hypothesizer)
Category: **cross-domain bridge** — finite information counting (double powerset) meets
phylogenetic agreement and the pigeonhole principle, feeding an iterated-exponential tower.

1. **Bold / named-problem:** the number of trees needed to *avoid* a repeated restriction on
   `a` leaves is governed exactly by the double exponential `2^(2^a)`; this is the atomic
   step of the fourfold-iterated bound.
2. **Bold:** the pigeonhole threshold is sharp in *form* — beyond `2^(2^a)` trees a repeated
   induced system, hence an agreeing pair, is unavoidable regardless of tree shape.
3. **Structural:** the iterated exponential tower `iterExp` is strictly increasing at every
   level and monotone in the base, so composing the atomic step four times is well defined
   and lands above every intermediate value.
4. **Bridge:** `restrict` is monotone in the split system, so agreement counting respects
   sub-systems.

## Experiment (Experimenter)
The double-powerset containment `restrict T A ⊆ 𝒫(A)` was verified symbolically, giving the
double-exponential cardinality bound `2^(2^|A|)` by `card_powerset` twice.  The pigeonhole
step was obtained from `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` with the map
`i ↦ restrict (T i) A`.

## Analysis (Analyst)
Three layers separate cleanly: (i) a *containment* layer (restrictions live in the double
powerset), (ii) a *counting* layer (cardinalities), and (iii) a *tower* layer (arithmetic of
`iterExp`).  The pigeonhole result is the pivot connecting (ii) to phylogenetic agreement.

## Critique (Critic)
The counting bound counts *split systems*, not whole binary topologies; it is deliberately
not the paper's final quantitative estimate, only the atomic recursion step.  The pigeonhole
statement needs a strict inequality `2^(2^|A|) < k`; equality is genuinely insufficient,
which is why the tower grows.  All statements are shape-agnostic: no binary-degree or
compatibility hypothesis is smuggled in.

## Synthesis (Principal Investigator)
Containment, double-exponential counting, the pigeonhole pivot, and the arithmetic of the
iterated tower form a reusable quantitative interface: exactly the pieces a compatibility-
sensitive refinement must iterate four times to reach the Snir–Yuster upper bound.
-/

open Finset

namespace AgreementSubtrees

variable {α ι : Type*} [DecidableEq α]

/-! ### Containment layer -/



/-! ### Counting layer: the double exponential -/




/-! ### Tower layer: the iterated exponential -/

/-- The iterated exponential tower: `iterExp 0 a = a` and `iterExp (n+1) a = 2^(iterExp n a)`.
The Snir–Yuster upper bound lives at height four, `iterExp 4`. -/
def iterExp : ℕ → ℕ → ℕ
  | 0, a => a
  | n + 1, a => 2 ^ (iterExp n a)










/-! ### Bridge to the pigeonhole threshold via the tower -/


end AgreementSubtrees

/-! ### Examples, generalizations, and boundaries -/

section Examples

open AgreementSubtrees

-- Concrete instantiation of the tower.
-- The pigeonhole threshold on two retained leaves: `2^(2^2) = 16` trees can still be
-- pairwise distinct on those two leaves; the bound is a genuine double exponential.
/-
**Generalization.**  The containment and counting layers use no property of the split
systems beyond being finite sets of subsets, so they extend verbatim to any finite
labelled combinatorial object whose restriction is a subset operation.  The pigeonhole
pivot then applies to any family indexed by a set larger than the double powerset.

**Boundary / limit case.**  The strict inequality in `exists_agreeing_pair` cannot be
relaxed to `≤`: with exactly `2^(2^|A|)` trees one can, in principle, realize every element
of the double powerset once, leaving no repeated restriction.  This boundary is precisely
what forces the exponential to be *iterated*: each level only reduces the problem to a
strictly smaller — but still doubly exponential — number of trees, so four levels are
needed to descend to a common quartet.
-/

end Examples


