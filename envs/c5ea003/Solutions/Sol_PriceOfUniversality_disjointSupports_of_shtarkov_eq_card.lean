-- Prove2me | solution 1 for PriceOfUniversality.disjointSupports_of_shtarkov_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:03:09.569845+00:00
-- url     : https://prove2.me/submissions/40917c47-9dd1-495c-baaf-d040eacfdb30

-- Sol generated from Novelty/UniversalRedundancyRigidity.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
import Definitions.Def_Novelty_UniversalRedundancyMinimax
import Definitions.Def_Novelty_UniversalRedundancyShtarkov
import Theorems.Thm_PriceOfUniversality_exists_eq_maxLik
import Theorems.Thm_PriceOfUniversality_unique_positive_of_maxLik_eq_sum
/-
# The price of universality, IX: rigidity of the maximal price

`shtarkov_disjointSupports` showed that `m` perfectly distinguishable sources
cost exactly `log₂ m` bits of universality — the cost of naming the source.
Here we prove the **converse**, and hence a rigidity theorem:

  `S(P) = m`  ⟺  the `m` sources have pairwise disjoint supports,

and, in strict form, **every genuinely overlapping class is strictly cheaper**
than naming its members:

  `¬ DisjointSupports P  →  S(P) < m`  and  `log₂ S(P) < log₂ m`.

So the naive "one code per model, plus a label" scheme is optimal *only* in the
degenerate case where the models never produce the same data; as soon as two
sources share a possible message the universal code strictly beats the labelling
scheme.  This is the precise sense in which the price of universality is a
measure of *statistical distinguishability*, not of class cardinality.
-/

open PriceOfUniversality

open Finset Real

variable {A : Type*} [Fintype A] [Nonempty A]
variable {Θ : Type*} [Fintype Θ] [Nonempty Θ]

omit [Nonempty A] in
/-- The maximum likelihood at a message never exceeds the total mass the class
puts on that message. -/
theorem maxLik_le_sum (p : Θ → A → ℝ) (hp : ∀ θ, IsPMF (p θ)) (a : A) :
    maxLik p a ≤ ∑ θ, p θ a := by
  obtain ⟨θ₀, hθ₀⟩ := exists_eq_maxLik p a
  rw [hθ₀]
  exact Finset.single_le_sum (f := fun θ => p θ a) (fun θ _ => (hp θ).nonneg a) (mem_univ θ₀)








open PriceOfUniversality in
omit [Nonempty A] in
theorem solution{p : Θ → A → ℝ} (hp : ∀ θ, IsPMF (p θ))
    (h : shtarkov p = Fintype.card Θ) : DisjointSupports p := by
  have hle : ∀ a ∈ (univ : Finset A), maxLik p a ≤ ∑ θ, p θ a :=
    fun a _ => maxLik_le_sum p hp a
  have htot : ∑ a, maxLik p a = ∑ a, ∑ θ, p θ a := by
    have hsum : ∑ a, ∑ θ, p θ a = (Fintype.card Θ : ℝ) := by
      calc ∑ a, ∑ θ, p θ a = ∑ _θ : Θ, (1:ℝ) := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun θ _ => (hp θ).total
        _ = Fintype.card Θ := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, mul_one]
    rw [hsum, ← h, shtarkov]
  have hpt : ∀ a ∈ (univ : Finset A), maxLik p a = ∑ θ, p θ a :=
    (Finset.sum_eq_sum_iff_of_le hle).1 htot
  intro θ θ' a hne hpos
  exact unique_positive_of_maxLik_eq_sum hp a (hpt a (mem_univ a)) θ θ' hne hpos
