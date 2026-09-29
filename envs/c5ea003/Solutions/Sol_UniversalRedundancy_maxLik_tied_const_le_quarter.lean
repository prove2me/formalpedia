-- Prove2me | solution 1 for UniversalRedundancy.maxLik_tied_const_le_quarter
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:27:59.031198+00:00
-- url     : https://prove2.me/submissions/27dce135-5c25-4537-84eb-3aa575090b03

-- Sol generated from MachineLearning/UniversalRedundancy/MemorylessStrict.lean
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_MemorylessStrict
import Definitions.Def_MachineLearning_UniversalRedundancy_Products
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
import Theorems.Thm_UniversalRedundancy_SourceClass_maxLik_le
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


omit [DecidableEq A] [Nonempty A] in
/-- Every simplex coordinate is at most `1`. -/
lemma simplex_le_one (θ : Simplex A) (a : A) : θ.1 a ≤ 1 := by
  have h := Finset.single_le_sum (f := fun b => θ.1 b)
    (fun b _ => θ.2.1 b) (Finset.mem_univ a)
  rw [θ.2.2] at h
  exact h

omit [Nonempty A] in
/-- Two distinct simplex coordinates sum to at most `1`. -/
lemma simplex_pair_le_one {θ : Simplex A} {a b : A} (hab : a ≠ b) :
    θ.1 a + θ.1 b ≤ 1 := by
  classical
  have h2 : ∑ c ∈ ({a, b} : Finset A), θ.1 c ≤ ∑ c, θ.1 c :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun c _ _ => θ.2.1 c
  rw [Finset.sum_pair hab, θ.2.2] at h2
  exact h2




/-! ## The length-one class sits at the upper rigidity endpoint -/


/-! ## The block decomposition is an isomorphism -/


/-! ## Strictness -/






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
open UniversalRedundancy in
theorem solution{n₁ n₂ : ℕ} (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂)
    {a b : A} (hab : a ≠ b) :
    (tiedProdClass (iidClass A n₁) (iidClass A n₂)).maxLik
        ((fun _ => a : Fin n₁ → A), (fun _ => b : Fin n₂ → A)) ≤ 1 / 4 := by
  classical
  refine SourceClass.maxLik_le _ fun θ => ?_
  have hprob : (tiedProdClass (iidClass A n₁) (iidClass A n₂)).prob θ
      ((fun _ => a : Fin n₁ → A), (fun _ => b : Fin n₂ → A))
      = θ.1 a ^ n₁ * θ.1 b ^ n₂ := by
    show (∏ _i : Fin n₁, θ.1 a) * ∏ _j : Fin n₂, θ.1 b = θ.1 a ^ n₁ * θ.1 b ^ n₂
    simp
  rw [hprob]
  have ha : θ.1 a ^ n₁ ≤ θ.1 a := by
    calc θ.1 a ^ n₁ ≤ θ.1 a ^ 1 :=
          pow_le_pow_of_le_one (θ.2.1 a) (simplex_le_one θ a) hn₁
      _ = θ.1 a := pow_one _
  have hb : θ.1 b ^ n₂ ≤ θ.1 b := by
    calc θ.1 b ^ n₂ ≤ θ.1 b ^ 1 :=
          pow_le_pow_of_le_one (θ.2.1 b) (simplex_le_one θ b) hn₂
      _ = θ.1 b := pow_one _
  have hsum : θ.1 a + θ.1 b ≤ 1 := simplex_pair_le_one hab
  have hpa : 0 ≤ θ.1 a ^ n₁ := pow_nonneg (θ.2.1 a) _
  have hpb : 0 ≤ θ.1 b ^ n₂ := pow_nonneg (θ.2.1 b) _
  nlinarith [θ.2.1 a, θ.2.1 b, sq_nonneg (θ.1 a - θ.1 b)]
