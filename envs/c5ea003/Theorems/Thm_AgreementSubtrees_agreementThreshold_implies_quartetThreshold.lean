-- Prove2me | Theorems.Thm_AgreementSubtrees_agreementThreshold_implies_quartetThreshold
-- name    : AgreementSubtrees.agreementThreshold_implies_quartetThreshold
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T14:57:11.306591+00:00
-- url     : https://prove2.me/theorems/81e96e30-fb10-40ab-b0a5-58fdad1421b1
-- title:
--   A threshold for an `n`-leaf common subtree (`n ≥ 4`) is automatically a threshold
-- statement:
--   A threshold for an `n`-leaf common subtree (`n ≥ 4`) is automatically a threshold
--   for a common quartet. This is the formal implication used to pass from the paper's
--   multiple-tree MAST upper bound to its upper bound on `h(k)`.
--
--   ```lean
--   theorem AgreementSubtrees.agreementThreshold_implies_quartetThreshold{N k n : ℕ} (hn : 4 ≤ n)
--       (h : IsAgreementThreshold N k n) : IsAgreementThreshold N k 4 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/Core.lean#L134

-- Thm stub generated from Novelty/Core.lean
import Mathlib
import Definitions.Def_Novelty_Core

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

theorem AgreementSubtrees.agreementThreshold_implies_quartetThreshold{N k n : ℕ} (hn : 4 ≤ n)
    (h : IsAgreementThreshold N k n) : IsAgreementThreshold N k 4 := by sorry
