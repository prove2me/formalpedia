-- Prove2me | solution 1 for UniversalRedundancy.shtarkovSum_iidClass_lt_pow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:36:13.1439+00:00
-- url     : https://prove2.me/submissions/e4000ea3-8cf6-441f-8db4-47d6bab94191

-- Sol generated from MachineLearning/UniversalRedundancy/MemorylessStrict.lean
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_MemorylessStrict
import Definitions.Def_MachineLearning_UniversalRedundancy_Products
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
import Theorems.Thm_UniversalRedundancy_SourceClass_le_maxLik
import Theorems.Thm_UniversalRedundancy_SourceClass_maxLik_le_one
import Theorems.Thm_UniversalRedundancy_maxLik_tied_const_le_quarter
import Theorems.Thm_UniversalRedundancy_shtarkovSum_iidClass_eq_card_one
import Theorems.Thm_UniversalRedundancy_shtarkovSum_iidClass_eq_tied
import Theorems.Thm_UniversalRedundancy_shtarkovSum_tiedProdClass_lt_of_maxLik_lt
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




omit [Nonempty A] in
/-- The point mass at `a` gives the constant string `aa…a` likelihood `1`. -/
lemma prob_iidClass_const_eq_one (n : ℕ) (a : A) :
    (iidClass A n).prob (deltaSimplex a) (fun _ => a) = 1 := by
  show ∏ _i : Fin n, (deltaSimplex a).1 a = 1
  simp [deltaSimplex]

/-- Hence the maximum-likelihood envelope of a constant string is `1`. -/
lemma maxLik_iidClass_const (n : ℕ) (a : A) :
    (iidClass A n).maxLik (fun _ => a) = 1 :=
  le_antisymm ((iidClass A n).maxLik_le_one _)
    (by
      have := (iidClass A n).le_maxLik (deltaSimplex a) (fun _ => a)
      rwa [prob_iidClass_const_eq_one n a] at this)


/-! ## The length-one class sits at the upper rigidity endpoint -/


/-! ## The block decomposition is an isomorphism -/


/-! ## Strictness -/


/-- **Strict submultiplicativity of the memoryless price.**  For an alphabet
with at least two letters, splitting a message into two non-empty blocks is
*strictly* cheaper than treating the blocks as independently parametrised:
`Cₛ(n₁+n₂) < Cₛ(n₁) · Cₛ(n₂)`. -/
theorem shtarkovSum_iidClass_strict_submultiplicative (hA : 2 ≤ Fintype.card A)
    {n₁ n₂ : ℕ} (hn₁ : 1 ≤ n₁) (hn₂ : 1 ≤ n₂) :
    (iidClass A (n₁ + n₂)).shtarkovSum
      < (iidClass A n₁).shtarkovSum * (iidClass A n₂).shtarkovSum := by
  classical
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (α := A) (by omega)
  rw [shtarkovSum_iidClass_eq_tied n₁ n₂]
  refine shtarkovSum_tiedProdClass_lt_of_maxLik_lt (iidClass A n₁) (iidClass A n₂)
    (x₁ := fun _ => a) (x₂ := fun _ => b) ?_
  have hq := maxLik_tied_const_le_quarter (A := A) hn₁ hn₂ hab
  rw [maxLik_iidClass_const n₁ a, maxLik_iidClass_const n₂ b]
  linarith




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
theorem solution(hA : 2 ≤ Fintype.card A) :
    ∀ n : ℕ, 2 ≤ n → (iidClass A n).shtarkovSum < (Fintype.card A : ℝ) ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      have h := shtarkovSum_iidClass_strict_submultiplicative (A := A) hA
        (n₁ := 1) (n₂ := 1) le_rfl le_rfl
      rw [shtarkovSum_iidClass_eq_card_one] at h
      calc (iidClass A 2).shtarkovSum
          < (Fintype.card A : ℝ) * (Fintype.card A : ℝ) := h
        _ = (Fintype.card A : ℝ) ^ 2 := by ring
  | succ n hn ih =>
      have hstep := shtarkovSum_iidClass_strict_submultiplicative (A := A) hA
        (n₁ := n) (n₂ := 1) (by omega) le_rfl
      rw [shtarkovSum_iidClass_eq_card_one] at hstep
      have hcard : (0 : ℝ) < (Fintype.card A : ℝ) := by
        have : (0 : ℕ) < Fintype.card A := by omega
        exact_mod_cast this
      calc (iidClass A (n + 1)).shtarkovSum
          < (iidClass A n).shtarkovSum * (Fintype.card A : ℝ) := hstep
        _ < (Fintype.card A : ℝ) ^ n * (Fintype.card A : ℝ) := by
            exact mul_lt_mul_of_pos_right ih hcard
        _ = (Fintype.card A : ℝ) ^ (n + 1) := by ring
