-- Prove2me | Definitions.Def_MachineLearning_UniversalRedundancy_MemorylessStrict
-- name    : MachineLearning_UniversalRedundancy_MemorylessStrict
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:17:49.042419+00:00
-- url     : https://prove2.me/theorems/d2e9774c-dfe8-4aa1-8a6c-6f9bf3a62d97
-- title:
--   Aether Catalog definitions — MachineLearning_UniversalRedundancy_MemorylessStrict
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.UniversalRedundancy.MemorylessStrict`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/UniversalRedundancy/MemorylessStrict.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Price of Universality IX: the memoryless price is *strictly* subadditive

Ninth instalment of the thread.  Part VII proved that the Shtarkov sum of the
memoryless class is submultiplicative in the block length,
`Cₛ(n₁ + n₂) ≤ Cₛ(n₁) · Cₛ(n₂)`, which is exactly what Fekete's lemma needs.
Part VIII turned the *equality case* of that induction into a checkable
criterion (`shtarkovSum_tiedProdClass_eq_iff`): equality holds iff every pair of
block outcomes admits a **common maximum-likelihood parameter**.

Here that criterion is cashed in.  For an alphabet with at least two letters the
two constant strings `aaa…a` and `bbb…b` have *no* common maximiser — the
maximiser of the first block is the point mass at `a`, that of the second the
point mass at `b`, and a probability vector cannot put mass `1` on two distinct
letters.  Hence the inequality of Part VII is **strict at every split**.

## Central Idea

Combining
* `shtarkovSum_iidClass_eq_card_one` : `Cₛ(1) = #A` (the length-one memoryless
  class is the point-mass class in disguise, sitting at the *upper* rigidity
  endpoint of Part VIII), and
* strictness at every split,

induction gives `Cₛ(n) < (#A)^n` for `n ≥ 2`: universal coding of a memoryless
source is *strictly* cheaper than coding each symbol with its own free
parameter, and the deficit compounds with every block.  This is the qualitative
content behind the `O(log n)` upper bound of Part II — the exponential price
`(#A)^n` of "one parameter per symbol" collapses to a polynomial one because the
blocks are *tied*.

## Main Results

* `deltaSimplex`, `prob_iidClass_const_eq_one`, `maxLik_iidClass_const` — point
  masses saturate the likelihood of a constant string
* `prob_eq_one_iff_coord`, `maxLik_tied_const_le_quarter` — a parameter that
  maximises a constant string must be the point mass, so two constant strings on
  distinct letters leave the tied envelope below `1/4`
* `shtarkovSum_iidClass_eq_card_one` — `Cₛ(1) = #A`
* `shtarkovSum_iidClass_eq_tied` — the length-`n₁+n₂` class *is* the tied
  product of its two blocks (the relabelling of Part VII is an isomorphism)
* `shtarkovSum_iidClass_strict_submultiplicative` — `Cₛ(n₁+n₂) < Cₛ(n₁)·Cₛ(n₂)`
  for `#A ≥ 2` and `n₁, n₂ ≥ 1`
* `iid_price_strictly_subadditive` — the bit form
* `shtarkovSum_iidClass_lt_pow` — `Cₛ(n) < (#A)^n` for `n ≥ 2`

## Application Keywords

universal coding, Shtarkov sum, memoryless sources, strict subadditivity,
Fekete's lemma, method of types
-/


open Finset Real

namespace UniversalRedundancy

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-! ## Point masses inside the simplex -/

/-- The point mass at `a`, as a member of the memoryless parameter simplex. -/
def deltaSimplex (a : A) : Simplex A :=
  ⟨fun b => if b = a then 1 else 0, fun b => by by_cases h : b = a <;> simp [h], by simp⟩






/-! ## The length-one class sits at the upper rigidity endpoint -/


/-! ## The block decomposition is an isomorphism -/


/-! ## Strictness -/





end UniversalRedundancy

/-! ## Lab notes (exact Bernoulli Shtarkov sums)

`Cₛ(n) = ∑_k C(n,k) (k/n)^k ((n-k)/n)^{n-k}` for the binary memoryless class,
evaluated exactly in `ℚ`:

| `n` | 1 | 2   | 3    | 4      | 5        |
|-----|---|-----|------|--------|----------|
| `Cₛ`| 2 | 5/2 | 26/9 | 103/32 | 2194/625 |

Against `Cₛ(1)^n = 2^n = 2, 4, 8, 16, 32` the deficit is already a factor `1.6`
at `n = 2` and grows to a factor `9.1` at `n = 5`: the strict inequality proved
in `shtarkovSum_iidClass_lt_pow` is far from tight, which is what
Direction 3 of `FUTURE_DIRECTIONS.md` proposes to quantify.
-/


