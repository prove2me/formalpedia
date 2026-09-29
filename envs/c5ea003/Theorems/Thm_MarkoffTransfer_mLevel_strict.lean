-- Prove2me | Theorems.Thm_MarkoffTransfer_mLevel_strict
-- name    : MarkoffTransfer.mLevel_strict
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:54:14.902314+00:00
-- url     : https://prove2.me/theorems/d3bf1471-8751-49c3-b78f-e6de63a80447
-- title:
--   MLevel strict
-- statement:
--   Formal statement of `MarkoffTransfer.mLevel_strict` from the Aether Catalog (Cryptography). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem MarkoffTransfer.mLevel_strict: ∀ (n : ℕ), ∀ t ∈ mLevel n, StrictM t := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/MarkoffTransfer/MarkoffFreeBinary.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/MarkoffTransfer/MarkoffFreeBinary.lean#L195

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






/-! ## Level counts: `2 ^ n` -/

theorem MarkoffTransfer.mLevel_strict: ∀ (n : ℕ), ∀ t ∈ mLevel n, StrictM t := by sorry
