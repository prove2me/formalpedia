-- Prove2me | solution 1 for UniversalRedundancy.iid_redundancy_bits_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:25:06.040548+00:00
-- url     : https://prove2.me/submissions/79bb61f1-a44d-45b0-9c56-725b6c5d0226

-- Sol generated from MachineLearning/UniversalRedundancy/Types.lean
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
import Theorems.Thm_UniversalRedundancy_SourceClass_le_maxLik
import Theorems.Thm_UniversalRedundancy_SourceClass_nmlCodeLength_le
import Theorems.Thm_UniversalRedundancy_SourceClass_shtarkovSum_le_of_product_form
import Theorems.Thm_UniversalRedundancy_SourceClass_shtarkovSum_pos
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Price of Universality II: parametric classes pay only `O(log n)`

Continuation of `MachineLearning.UniversalRedundancy.Core`.  There the minimax
redundancy of a source class was identified *exactly* with `log₂ Cₛ`, the log of
the Shtarkov sum.  Here we bound `Cₛ` for the classes that matter in practice —
memoryless (i.i.d.) sources and Markov sources — and obtain closed-form bounds
in the message length `n` and the *class complexity*.

## Central Idea

The abstract engine is a **sufficient statistic** bound: if the likelihood
`p_θ x` depends on `x` only through a statistic `T x` taking `N` values, then

`Cₛ ≤ N`.

Indeed the fibre of `T` over a value `s` has some cardinality `k`, on which the
maximum likelihood is a constant `M`; since `k · p_θ x ≤ 1` for every `θ`, also
`k · M ≤ 1`, so each fibre contributes at most `1` to `∑ₓ maxₜ p_θ x`.

For a class whose likelihood is a product of `m` factors drawn from a finite
"feature alphabet" `B` (times a factor depending on a finite initial statistic
in `C`), the counts of the features form such a statistic, giving

`Cₛ ≤ #C · (m+1) ^ #B`.

Specialising: memoryless sources over an alphabet `A` on messages of length `n`
give `Cₛ ≤ (n+1) ^ #A`, and first-order Markov sources give
`Cₛ ≤ #A · (n+1) ^ (#A · #A)`.  In bits: the price of universality is at most
`#A · log₂ (n+1)` resp. `log₂ #A + #A² · log₂ (n+1)` bits — logarithmic in `n`,
matching the Rissanen-style `(d/2) log₂ n` rate up to the constant factor `2`
in front of the parameter dimension `d`.

## Main Results

* `SourceClass.shtarkovSum_le_card_statistic` — sufficient-statistic bound
* `SourceClass.shtarkovSum_le_of_product_form` — counting bound for product
  likelihoods, `Cₛ ≤ #C · (m+1) ^ #B`
* `iidClass`, `shtarkovSum_iidClass_le` — memoryless sources: `Cₛ ≤ (n+1) ^ #A`
* `markovClass`, `shtarkovSum_markovClass_le` — Markov sources:
  `Cₛ ≤ #A · (n+1) ^ (#A * #A)`
* `iid_redundancy_bits_le`, `markov_redundancy_bits_le` — the bit-level
  statements: a single universal code is within `#A log₂(n+1) + 1` bits of the
  code tailored to the true memoryless source, for *every* source and *every*
  message
* `iid_redundancy_rate_tendsto_zero` — the per-symbol price of universality
  tends to `0`: specialisation buys a vanishing fraction of the message

## Application Keywords

method of types, sufficient statistic, Rissanen redundancy, Markov sources,
universal coding, parametric class complexity
-/


open Finset Real

open UniversalRedundancy

/-! ## Sufficient-statistic bound on the Shtarkov sum -/

open SourceClass

variable {X : Type*} [Fintype X] {Θ : Type*} (S : SourceClass X Θ)


/-! ## Counting statistic for product likelihoods -/




open SourceClass

variable {X : Type*} [Fintype X] {Θ : Type*} (S : SourceClass X Θ)



/-! ## Memoryless (i.i.d.) sources -/



variable {A : Type*} [Fintype A] [DecidableEq A]


/-- **Memoryless sources: `Cₛ ≤ (n+1) ^ #A`.**  The price of universality for
the whole i.i.d. class is at most `#A · log₂ (n+1)` bits, regardless of how
finely the parameter is tuned. -/
theorem shtarkovSum_iidClass_le [Nonempty A] (n : ℕ) :
    (iidClass A n).shtarkovSum ≤ ((n + 1 : ℕ) : ℝ) ^ (Fintype.card A) := by
  classical
  have := (iidClass A n).shtarkovSum_le_of_product_form
    (B := A) (C := Unit) (m := n) (feat := fun x j => x j) (init := fun _ => ())
    (g := fun θ a => θ.1 a) (h := fun _ _ => 1) (by intro θ x; simp [iidClass])
  simpa using this

/-- Every message has positive maximum likelihood in the i.i.d. class (witness:
the uniform parameter), so the NML code is well defined. -/
lemma maxLik_iidClass_pos [Nonempty A] (n : ℕ) (x : Fin n → A) :
    0 < (iidClass A n).maxLik x := by
  have hA : (0 : ℝ) < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos
  set θ : Simplex A := Classical.arbitrary (Simplex A) with hθ
  have hpos : 0 < (iidClass A n).prob
      (⟨fun _ => (Fintype.card A : ℝ)⁻¹, fun _ => by positivity, by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp⟩ : Simplex A) x := by
    simp only [iidClass]
    exact Finset.prod_pos fun i _ => by positivity
  exact lt_of_lt_of_le hpos ((iidClass A n).le_maxLik _ x)




open UniversalRedundancy in
theorem solution[Nonempty A] (n : ℕ) (θ : Simplex A) (x : Fin n → A)
    (hx : 0 < (iidClass A n).prob θ x) :
    ((iidClass A n).nmlCodeLength x : ℝ)
      ≤ logb 2 (1 / (iidClass A n).prob θ x)
        + (Fintype.card A : ℝ) * logb 2 ((n : ℝ) + 1) + 1 := by
  have h1 := (iidClass A n).nmlCodeLength_le (maxLik_iidClass_pos n) hx
  have h2 : logb 2 (iidClass A n).shtarkovSum
      ≤ (Fintype.card A : ℝ) * logb 2 ((n : ℝ) + 1) := by
    have hC := shtarkovSum_iidClass_le (A := A) n
    have hbase : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hbase] at hC
    have hle : logb 2 (iidClass A n).shtarkovSum
        ≤ logb 2 (((n : ℝ) + 1) ^ (Fintype.card A)) :=
      Real.logb_le_logb_of_le (by norm_num) (iidClass A n).shtarkovSum_pos hC
    rwa [Real.logb_pow] at hle
  linarith
