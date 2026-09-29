-- Prove2me | Theorems.Thm_MarkoffTransfer_mEval_injective
-- name    : MarkoffTransfer.mEval_injective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:54:17.498598+00:00
-- url     : https://prove2.me/theorems/3654e8a2-1bf2-481f-9d37-e52e9fa60903
-- title:
--   Freeness of the Markoff tree.
-- statement:
--   **Freeness of the Markoff tree.**  Distinct binary words give distinct Markoff triples;
--   this is the rank-`2` counterpart of the Berggren free monoid of rank `3`.
--
--   ```lean
--   theorem MarkoffTransfer.mEval_injective: Function.Injective mEval := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/MarkoffTransfer/MarkoffFreeBinary.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/MarkoffTransfer/MarkoffFreeBinary.lean#L160

-- Thm stub generated from Cryptography/MarkoffTransfer/MarkoffFreeBinary.lean
import Mathlib
import Definitions.Def_Cryptography_MarkoffTransfer_MarkoffCore
import Definitions.Def_Cryptography_MarkoffTransfer_MarkoffFreeBinary

/-!
# The Markoff Tree is a Free **Binary** Tree

The Berggren tree of primitive Pythagorean triples is a free **ternary** tree: the three
Berggren moves generate a free monoid of rank `3` (see
`Cryptography/BerggrenTrees/BerggrenFreeMonoid.lean`, `evalPair_injective`).

Here we prove the exact Markoff analogue, which is the "transfer" of that machinery to the
Markoff side — with rank `2` instead of `3`:

* `parent_childL` / `parent_childR` — **unique parent**: the descent map inverts both
  ascending Vieta moves.  This is the Markoff counterpart of `actGen_unique_parent`.
* `childL_ne_childR` — the two children of a strictly ordered node are distinct.
* `mEval_injective` — **freeness**: the evaluation of binary words at the root `(1,2,5)`
  is injective, so the Markoff tree is a free binary tree.
* `mLevel_card` — level `n` of the Markoff tree has exactly `2 ^ n` nodes.

Every node of the tree is a strictly ordered positive Markoff triple (`StrictM`), so the
whole development stays inside the Markoff surface.
-/

open MarkoffTransfer

/-! ## Strictly ordered Markoff triples -/




/-! ## The two ascending Vieta moves -/





/-! ## Children are nodes -/




/-! ## Unique parent -/







/-! ## Freeness: the tree of binary words -/

theorem MarkoffTransfer.mEval_injective: Function.Injective mEval := by sorry
