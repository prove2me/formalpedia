-- Prove2me | Theorems.Thm_AgreementSubtrees_mem_restrict_subset
-- name    : AgreementSubtrees.mem_restrict_subset
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T14:57:21.448178+00:00
-- url     : https://prove2.me/theorems/1e9bd05f-5314-4e64-bc20-a245052953c8
-- title:
--   Mem restrict subset
-- statement:
--   Formal statement of `AgreementSubtrees.mem_restrict_subset` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem AgreementSubtrees.mem_restrict_subset{T : SplitSystem α} {A s : Finset α}
--       (hs : s ∈ restrict T A) : s ⊆ A := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/AgreementSubtreesMultiple.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/AgreementSubtreesMultiple.lean#L80

-- Thm stub generated from Novelty/AgreementSubtreesMultiple.lean
import Mathlib
import Definitions.Def_Novelty_AgreementSubtreesMultiple
import Definitions.Def_Novelty_Core

/-!
# Multiple agreement subtrees: gluing, counting, and threshold transfer

The split-system representation turns restriction of a labelled phylogenetic tree into
intersection of every displayed split with the retained leaf set.  This chapter develops
three consequences used in the study of agreement subtrees for many trees:

* common agreement can be glued across two families sharing a tree;
* every restricted system is supported on the powerset of the retained leaves, giving a
  double-exponential bound on its number of displayed splits;
* any uniform bound forcing a larger common subtree transfers to the quartet problem,
  independently of the analytic form of the bound (in particular, to fourfold iterated
  exponential bounds).

The results apply to arbitrary finite split systems; binary compatibility assumptions are
not needed for these restriction-algebra steps.

-- !-- Lab Notes -- !--
## Hypothesis (Hypothesizer)
The selected target category is **cross-domain bridge**: finite-set restriction algebra,
overlap connectivity, and information counting are combined with phylogenetic agreement.
The conjectures below are ranked by expected impact.

1. **Named-problem subtask, bold:** four rounds of compatible-signature refinement suffice
   to recover the fourfold exponential upper bound for the multiple-tree MAST problem.
2. **Named-problem subtask, bold:** probabilistic packings of quartet signatures give the
   optimal exponential rate in the lower bound for the common-quartet threshold `h(k)`.
3. **Named-problem subtask, bold:** for fixed small `k`, all extremal families defining
   `h(k)` fall into finitely many explicit relabelling orbits.
4. **Connectivity bridge:** common-restriction witnesses should glue along every connected
   overlap pattern; the chain case is the first falsifiable instance.
5. **Information bridge:** a restriction to `a` leaves should contain at most `2^a` distinct
   split sides, while binary compatibility should permit a sharper topology count.
6. **Ramsey bridge:** every bound for a common subtree of size at least four should
   automatically be a bound for a common quartet.

## Experiment (Experimenter)
The restriction operation was tested symbolically under nested leaf deletion and under
unions of split systems.  The gluing statement survives exactly when the two tree families
share an index: the shared restriction identifies their two witnesses.  Counting split
sides reduces to the powerset identity `|𝒫(A)| = 2^|A|`.

## Analysis (Analyst)
The surviving statements separate into a categorical layer (restriction composition and
witness gluing), an information-theoretic layer (powerset bounds), and an extremal layer
(threshold transfer).  The compatibility and binary-degree conditions enter only beyond
this interface, when one seeks the paper's quantitative fourfold exponential estimate.

## Critique (Critic)
The overlap hypothesis in the gluing theorem is essential: two disjoint singleton families
may choose different restrictions.  The powerset estimate counts split sides rather than
whole tree topologies, so it is deliberately not advertised as the paper's final bound.
The threshold theorem assumes, rather than proves, a quantitative common-subtree bound;
it rigorously isolates the implication from that bound to the quartet bound.

## Synthesis (Principal Investigator)
Restriction functoriality, overlap gluing, finite information bounds, and quartet transfer
form a reusable interface between phylogenetic agreement and finite Ramsey counting.  This
interface identifies precisely where future work must add compatibility-sensitive counting.
-/

open Finset

open AgreementSubtrees

variable {α ι : Type*} [DecidableEq α] [DecidableEq ι]

/-
Restriction distributes over union of split systems.
-/

/-
Every split side surviving restriction is a subset of the retained leaf set.
-/

theorem AgreementSubtrees.mem_restrict_subset{T : SplitSystem α} {A s : Finset α}
    (hs : s ∈ restrict T A) : s ⊆ A := by sorry
