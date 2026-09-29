-- Prove2me | Theorems.Thm_UniversalRedundancy_maxLik_tied_const_le_quarter
-- name    : UniversalRedundancy.maxLik_tied_const_le_quarter
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T20:00:37.536561+00:00
-- url     : https://prove2.me/theorems/abdd83a4-5b81-4b30-bd00-efb9f818fc4d
-- title:
--   Quantitative failure of a common maximiser.
-- statement:
--   **Quantitative failure of a common maximiser.**  For two distinct letters,
--   no memoryless parameter can give both constant strings `aa…a` and `bb…b` more
--   than a quarter of the likelihood they achieve separately: the tied envelope at
--   that pair is at most `1/4`, while the product of the block envelopes is `1`.
--
--   ```lean
--   theorem UniversalRedundancy.maxLik_tied_const_le_quarter{n₁ n₂ : ℕ} (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂)
--       {a b : A} (hab : a ≠ b) :
--       (tiedProdClass (iidClass A n₁) (iidClass A n₂)).maxLik
--           ((fun _ => a : Fin n₁ → A), (fun _ => b : Fin n₂ → A)) ≤ 1 / 4 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/UniversalRedundancy/MemorylessStrict.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/UniversalRedundancy/MemorylessStrict.lean#L159

-- Thm stub generated from MachineLearning/UniversalRedundancy/MemorylessStrict.lean
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_MemorylessStrict
import Definitions.Def_MachineLearning_UniversalRedundancy_Products
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

open UniversalRedundancy

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-! ## Point masses inside the simplex -/







/-! ## The length-one class sits at the upper rigidity endpoint -/


/-! ## The block decomposition is an isomorphism -/


/-! ## Strictness -/

theorem UniversalRedundancy.maxLik_tied_const_le_quarter{n₁ n₂ : ℕ} (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂)
    {a b : A} (hab : a ≠ b) :
    (tiedProdClass (iidClass A n₁) (iidClass A n₂)).maxLik
        ((fun _ => a : Fin n₁ → A), (fun _ => b : Fin n₂ → A)) ≤ 1 / 4 := by sorry
