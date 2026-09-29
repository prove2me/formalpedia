-- Prove2me | Definitions.Def_Bridges_LogisticCryptographyDeepening_BinaryPreimageTree
-- name    : Bridges_LogisticCryptographyDeepening_BinaryPreimageTree
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:28:51.694974+00:00
-- url     : https://prove2.me/theorems/bdd50e5c-2416-4f9a-8556-30565e09eb75
-- title:
--   Aether Catalog definitions — Bridges_LogisticCryptographyDeepening_BinaryPreimageTree
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.LogisticCryptographyDeepening.BinaryPreimageTree`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/LogisticCryptographyDeepening/BinaryPreimageTree.lean by skeleton subtraction
import Mathlib

/-!
# The complete binary inverse tree of the logistic map

For the parameter-four logistic map, every target strictly between zero and one has
`2^n` explicitly indexed, pairwise distinct real seeds that produce it after `n`
updates.  The index is an `n`-bit word.  Each bit selects one of the two inverse
branches, exposing a precise cryptographic ambiguity behind the chaotic dynamics.
-/

noncomputable section

namespace LogisticBinaryTree

open Set

/-- The parameter-four logistic map. -/
def logistic (x : ℝ) : ℝ := 4 * x * (1 - x)

/-- The lower inverse branch. -/
def lower (y : ℝ) : ℝ := (1 - Real.sqrt (1 - y)) / 2

/-- The upper inverse branch, reflected about `1/2`. -/
def upper (y : ℝ) : ℝ := (1 + Real.sqrt (1 - y)) / 2

/-- Select an inverse branch with one bit. -/
def branch (b : Bool) (y : ℝ) : ℝ := if b then upper y else lower y

/-- Decode an `n`-bit word as a depth-`n` preimage of `y`. -/
def inverseSeed : (n : ℕ) → (Fin n → Bool) → ℝ → ℝ
  | 0, _, y => y
  | n + 1, bits, y =>
      branch (bits 0) (inverseSeed n (fun i => bits i.succ) y)

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

/-
**Exponential preimage ambiguity.** For every interior target and every depth
`n`, there is an explicit injection from the `n`-bit key space into seeds in the
open unit interval, and every one of those seeds yields the target after exactly
`n` updates.
-/

/-
Once a decoded seed reaches its target, its entire future orbit is the target's
future orbit. Hence all indexed seeds have identical keystream suffixes from sample
`n` onward.
-/


/-
For positive depth, every interior target has at least two distinct interior
seeds which produce that target after exactly `n` updates.
-/

end LogisticBinaryTree


