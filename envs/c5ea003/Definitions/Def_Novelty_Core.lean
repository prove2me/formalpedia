-- Prove2me | Definitions.Def_Novelty_Core
-- name    : Novelty_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:00:32.915+00:00
-- url     : https://prove2.me/theorems/eaea77bd-486b-43df-8bf5-0bd0fba3d08a
-- title:
--   Aether Catalog definitions — Novelty_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/Core.lean by skeleton subtraction
import Mathlib

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

namespace AgreementSubtrees

variable {α ι : Type*} [DecidableEq α]

/-- A finite split encoding of a labelled phylogenetic tree. -/
abbrev SplitSystem (α : Type*) := Finset (Finset α)

/-- Restrict every split of a system to a set of retained leaves. -/
def restrict (T : SplitSystem α) (A : Finset α) : SplitSystem α :=
  T.image (fun s => s ∩ A)





/-- Two trees agree on `A` when their induced split systems on `A` coincide. -/
def AgreeOn (T U : SplitSystem α) (A : Finset α) : Prop :=
  restrict T A = restrict U A





/-- A family has a common induced subtree on `A` if all restrictions equal one witness. -/
def CommonAgreement (F : Finset ι) (T : ι → SplitSystem α) (A : Finset α) : Prop :=
  ∃ R : SplitSystem α, ∀ i ∈ F, restrict (T i) A = R





/-- `N` forces an `n`-leaf common agreement subtree for every `k`-indexed family. -/
def IsAgreementThreshold (N k n : ℕ) : Prop :=
  ∀ (T : Fin k → SplitSystem (Fin N)),
    ∃ A : Finset (Fin N), A.card = n ∧ CommonAgreement Finset.univ T A



/-
No agreement threshold can request more leaves than the ambient leaf set contains.
-/

/-
For one tree, the exact threshold condition is simply that the requested leaf set
fits in the ambient leaf set. This is the base case of the multiple-tree problem.
-/

end AgreementSubtrees


