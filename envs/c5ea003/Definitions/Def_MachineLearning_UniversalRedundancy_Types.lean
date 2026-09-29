-- Prove2me | Definitions.Def_MachineLearning_UniversalRedundancy_Types
-- name    : MachineLearning_UniversalRedundancy_Types
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:02:53.770365+00:00
-- url     : https://prove2.me/theorems/2a451fc1-8825-4e09-86e3-6484836bf5bb
-- title:
--   Aether Catalog definitions — MachineLearning_UniversalRedundancy_Types
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.UniversalRedundancy.Types`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/UniversalRedundancy/Types.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
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

namespace UniversalRedundancy

/-! ## Sufficient-statistic bound on the Shtarkov sum -/

namespace SourceClass

variable {X : Type*} [Fintype X] {Θ : Type*} (S : SourceClass X Θ)


/-! ## Counting statistic for product likelihoods -/

end SourceClass

/-- The count statistic of a feature word: how often each feature occurs. -/
def countStat {B : Type*} [DecidableEq B] {m : ℕ} (w : Fin m → B) (b : B) : Fin (m + 1) :=
  ⟨(univ.filter (fun j => w j = b)).card, by
    have : (univ.filter (fun j : Fin m => w j = b)).card ≤ Fintype.card (Fin m) :=
      le_trans (Finset.card_filter_le _ _) (le_of_eq (by simp))
    simp only [Fintype.card_fin] at this
    omega⟩


namespace SourceClass

variable {X : Type*} [Fintype X] {Θ : Type*} (S : SourceClass X Θ)


end SourceClass

/-! ## Memoryless (i.i.d.) sources -/

/-- The parameter space of a memoryless source over the alphabet `A`. -/
def Simplex (A : Type*) [Fintype A] : Type _ :=
  {θ : A → ℝ // (∀ a, 0 ≤ θ a) ∧ ∑ a, θ a = 1}

instance (A : Type*) [Fintype A] [Nonempty A] [DecidableEq A] :
    Nonempty (Simplex A) :=
  ⟨⟨fun _ => (Fintype.card A : ℝ)⁻¹, fun _ => by positivity, by
      have hA : (Fintype.card A : ℝ) ≠ 0 := by
        have : 0 < Fintype.card A := Fintype.card_pos
        positivity
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp⟩⟩

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The class of memoryless (i.i.d.) sources on messages of length `n`. -/
noncomputable def iidClass (A : Type*) [Fintype A] [DecidableEq A] (n : ℕ) :
    SourceClass (Fin n → A) (Simplex A) where
  prob θ x := ∏ i, θ.1 (x i)
  nonneg θ x := Finset.prod_nonneg fun i _ => θ.2.1 (x i)
  sum_one θ := by
    classical
    have := Finset.prod_univ_sum (fun _ : Fin n => (univ : Finset A))
      (fun _ (a : A) => θ.1 a)
    simp only [Fintype.piFinset_univ, θ.2.2, Finset.prod_const_one] at this
    simpa using this.symm





end UniversalRedundancy


