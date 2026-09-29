-- Prove2me | Theorems.Thm_LogisticBinaryTree_inverseSeed_injective
-- name    : LogisticBinaryTree.inverseSeed_injective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:50:50.526991+00:00
-- url     : https://prove2.me/theorems/4f52eb35-3608-4771-8d29-59db4c800820
-- title:
--   InverseSeed injective
-- statement:
--   Formal statement of `LogisticBinaryTree.inverseSeed_injective` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem LogisticBinaryTree.inverseSeed_injective(n : ℕ) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
--       Function.Injective (fun bits : Fin n → Bool => inverseSeed n bits y) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/LogisticCryptographyDeepening/BinaryPreimageTree.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/LogisticCryptographyDeepening/BinaryPreimageTree.lean#L96

-- Thm stub generated from Bridges/LogisticCryptographyDeepening/BinaryPreimageTree.lean
import Mathlib
import Definitions.Def_Bridges_LogisticCryptographyDeepening_BinaryPreimageTree

/-!
# The complete binary inverse tree of the logistic map

For the parameter-four logistic map, every target strictly between zero and one has
`2^n` explicitly indexed, pairwise distinct real seeds that produce it after `n`
updates.  The index is an `n`-bit word.  Each bit selects one of the two inverse
branches, exposing a precise cryptographic ambiguity behind the chaotic dynamics.
-/

noncomputable section

open LogisticBinaryTree

open Set






/-
Both explicit branches are genuine preimages.
-/

/-
Every branch maps the open unit interval back into it.
-/

/-
The two branches occupy disjoint halves of the unit interval.
-/

/-
Each individual inverse branch is injective on the open unit interval.
-/

/-
Every decoded seed remains strictly inside the unit interval.
-/

/-
Applying `n` logistic updates to a depth-`n` decoded seed recovers the target.
-/

/-
Distinct bit words decode to distinct seeds.  Thus no two paths in the inverse
binary tree merge before reaching their common target.
-/

theorem LogisticBinaryTree.inverseSeed_injective(n : ℕ) {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    Function.Injective (fun bits : Fin n → Bool => inverseSeed n bits y) := by sorry
