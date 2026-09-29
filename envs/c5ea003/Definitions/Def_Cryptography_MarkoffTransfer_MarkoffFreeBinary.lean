-- Prove2me | Definitions.Def_Cryptography_MarkoffTransfer_MarkoffFreeBinary
-- name    : Cryptography_MarkoffTransfer_MarkoffFreeBinary
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:20:23.299496+00:00
-- url     : https://prove2.me/theorems/50069c16-3484-4ee7-896f-f64423cb65e5
-- title:
--   Aether Catalog definitions — Cryptography_MarkoffTransfer_MarkoffFreeBinary
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.MarkoffTransfer.MarkoffFreeBinary`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/MarkoffTransfer/MarkoffFreeBinary.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_MarkoffTransfer_MarkoffCore

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

namespace MarkoffTransfer

/-! ## Strictly ordered Markoff triples -/

/-- A *node* of the Markoff tree: a strictly increasing positive Markoff triple whose top
entry is at least `5` (equivalently: any Markoff triple other than the three singular ones
`(1,1,1)`, `(1,1,2)`, `(1,2,2)`, up to ordering). -/
def StrictM (t : ℤ × ℤ × ℤ) : Prop :=
  0 < t.1 ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ 5 ≤ t.2.2 ∧ IsMarkoff t.1 t.2.1 t.2.2

/-- The root of the Markoff tree (the smallest non-singular triple). -/
def mRoot : ℤ × ℤ × ℤ := (1, 2, 5)


/-! ## The two ascending Vieta moves -/

/-- Left child: apply the Vieta move in the middle coordinate. -/
def childL (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (t.1, t.2.2, 3 * t.1 * t.2.2 - t.2.1)

/-- Right child: apply the Vieta move in the first coordinate. -/
def childR (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ := (t.2.1, t.2.2, 3 * t.2.1 * t.2.2 - t.1)

/-- The child selected by a bit. -/
def child : Bool → (ℤ × ℤ × ℤ) → ℤ × ℤ × ℤ
  | false => childL
  | true => childR

/-- The descent (parent) map: apply the Vieta move to the top coordinate and re-sort. -/
def mParent (t : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  if 3 * t.1 * t.2.1 - t.2.2 ≤ t.1 then (3 * t.1 * t.2.1 - t.2.2, t.1, t.2.1)
  else (t.1, 3 * t.1 * t.2.1 - t.2.2, t.2.1)

/-! ## Children are nodes -/




/-! ## Unique parent -/







/-! ## Freeness: the tree of binary words -/

/-- Evaluation of a binary word at the root: the Markoff analogue of `evalPair`. -/
def mEval : List Bool → ℤ × ℤ × ℤ
  | [] => mRoot
  | b :: w => child b (mEval w)





/-! ## Level counts: `2 ^ n` -/

/-- Level `n` of the Markoff tree, as a finite set of triples. -/
def mLevel : ℕ → Finset (ℤ × ℤ × ℤ)
  | 0 => {mRoot}
  | n + 1 => (mLevel n).image childL ∪ (mLevel n).image childR




end MarkoffTransfer


