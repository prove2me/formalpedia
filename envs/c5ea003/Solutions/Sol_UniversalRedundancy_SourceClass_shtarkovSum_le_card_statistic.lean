-- Prove2me | solution 1 for UniversalRedundancy.SourceClass.shtarkovSum_le_card_statistic
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:19:03.61324+00:00
-- url     : https://prove2.me/submissions/7cc955aa-489c-44cc-afe0-3923b4ee3080

-- Sol generated from MachineLearning/UniversalRedundancy/Types.lean
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Definitions.Def_MachineLearning_UniversalRedundancy_Types
import Theorems.Thm_UniversalRedundancy_SourceClass_maxLik_le
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







open UniversalRedundancy in
theorem solution[Nonempty Θ] {σ : Type*} [Fintype σ]
    [DecidableEq σ] (T : X → σ)
    (hT : ∀ θ x y, T x = T y → S.prob θ x = S.prob θ y) :
    S.shtarkovSum ≤ (Fintype.card σ : ℝ) := by
  classical
  have hfib : ∀ s : σ, ∑ x ∈ univ.filter (fun x => T x = s), S.maxLik x ≤ 1 := by
    intro s
    rcases Finset.eq_empty_or_nonempty (univ.filter (fun x => T x = s)) with he | hne
    · simp [he]
    obtain ⟨x0, hx0⟩ := hne
    have hx0' : T x0 = s := (Finset.mem_filter.mp hx0).2
    have hconstprob : ∀ θ, ∀ x ∈ univ.filter (fun x => T x = s),
        S.prob θ x = S.prob θ x0 := by
      intro θ x hx
      exact hT θ x x0 (by rw [(Finset.mem_filter.mp hx).2, hx0'])
    have hconst : ∀ x ∈ univ.filter (fun x => T x = s), S.maxLik x = S.maxLik x0 := by
      intro x hx
      unfold SourceClass.maxLik
      exact congrArg _ (funext fun θ => hconstprob θ x hx)
    set k : ℕ := (univ.filter (fun x => T x = s)).card with hk
    have hkpos : 0 < k := Finset.card_pos.mpr ⟨x0, hx0⟩
    have hmass : ∀ θ, (k : ℝ) * S.prob θ x0 ≤ 1 := by
      intro θ
      have h1 : ∑ x ∈ univ.filter (fun x => T x = s), S.prob θ x = (k : ℝ) * S.prob θ x0 := by
        rw [Finset.sum_congr rfl (hconstprob θ), Finset.sum_const, nsmul_eq_mul, hk]
      have h2 : ∑ x ∈ univ.filter (fun x => T x = s), S.prob θ x ≤ ∑ x, S.prob θ x :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun x _ _ => S.nonneg θ x
      rw [S.sum_one θ] at h2
      linarith [h1 ▸ h2]
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
    have hmaxle : S.maxLik x0 ≤ 1 / (k : ℝ) := by
      refine S.maxLik_le fun θ => ?_
      rw [le_div_iff₀ hkR]
      calc S.prob θ x0 * (k : ℝ) = (k : ℝ) * S.prob θ x0 := by ring
        _ ≤ 1 := hmass θ
    calc ∑ x ∈ univ.filter (fun x => T x = s), S.maxLik x
        = (k : ℝ) * S.maxLik x0 := by
          rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul, hk]
      _ ≤ (k : ℝ) * (1 / (k : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hmaxle hkR.le
      _ = 1 := by field_simp
  calc S.shtarkovSum
      = ∑ s : σ, ∑ x ∈ univ.filter (fun x => T x = s), S.maxLik x :=
        (Finset.sum_fiberwise univ T S.maxLik).symm
    _ ≤ ∑ _s : σ, (1 : ℝ) := Finset.sum_le_sum fun s _ => hfib s
    _ = (Fintype.card σ : ℝ) := by simp
