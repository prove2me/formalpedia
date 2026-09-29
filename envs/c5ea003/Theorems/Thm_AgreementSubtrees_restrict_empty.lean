-- Prove2me | Theorems.Thm_AgreementSubtrees_restrict_empty
-- name    : AgreementSubtrees.restrict_empty
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:57:15.68602+00:00
-- url     : https://prove2.me/theorems/792f6d25-c3be-4905-a5f2-7d71186b0975
-- title:
--   Restrict empty
-- statement:
--   Formal statement of `AgreementSubtrees.restrict_empty` from the Aether Catalog (Probability). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem AgreementSubtrees.restrict_empty(T : SplitSystem α) : restrict T ∅ = {∅} ∨ T = ∅ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/Core.lean#L31

-- Thm stub generated from Probability/Core.lean
import Mathlib
import Definitions.Def_Probability_Core

/-!
# Agreement subtrees: restriction and threshold infrastructure

A finite unrooted phylogenetic tree is determined by its nontrivial edge splits. This
file isolates the restriction algebra used in the multiple-tree maximum-agreement-
subtree problem. A `SplitSystem α` is represented extensionally as a finite family of
finite leaf sets (one consistently chosen side of each split). Restriction to a leaf set
intersects every split with that set. The results therefore apply more generally to
arbitrary finite split systems.

The principal structural theorem, `commonAgreement_iff_pairwise`, says that a leaf set
is a common agreement set for a nonempty family exactly when every pair of systems has
identical restriction there. We also prove heredity under taking smaller leaf sets and
the abstract transfer from any common-subtree threshold to a common-quartet threshold.
-/

open Finset

open AgreementSubtrees

variable {α ι : Type*} [DecidableEq α]



@[simp]

theorem AgreementSubtrees.restrict_empty(T : SplitSystem α) : restrict T ∅ = {∅} ∨ T = ∅ := by sorry
