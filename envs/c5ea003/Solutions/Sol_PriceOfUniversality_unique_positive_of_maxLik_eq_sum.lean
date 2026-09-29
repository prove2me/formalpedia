-- Prove2me | solution 1 for PriceOfUniversality.unique_positive_of_maxLik_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:59:26.916586+00:00
-- url     : https://prove2.me/submissions/7cb7cdf7-e7c0-477a-b98a-833f0b7e5803

-- Sol generated from Novelty/UniversalRedundancyRigidity.lean
import Mathlib
import Definitions.Def_Novelty_UniversalRedundancyCore
import Definitions.Def_Novelty_UniversalRedundancyShtarkov
import Theorems.Thm_PriceOfUniversality_exists_eq_maxLik
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









open PriceOfUniversality in
omit [Nonempty A] in
theorem solution{p : Θ → A → ℝ} (hp : ∀ θ, IsPMF (p θ)) (a : A)
    (h : maxLik p a = ∑ θ, p θ a) :
    ∀ θ θ' : Θ, θ ≠ θ' → 0 < p θ a → p θ' a = 0 := by
  classical
  obtain ⟨θ₀, hθ₀⟩ := exists_eq_maxLik p a
  have hsplit : ∑ ψ, p ψ a = p θ₀ a + ∑ ψ ∈ univ.erase θ₀, p ψ a :=
    (Finset.add_sum_erase univ (fun ψ => p ψ a) (mem_univ θ₀)).symm
  have hzero : ∑ ψ ∈ univ.erase θ₀, p ψ a = 0 := by
    rw [hθ₀] at h; rw [hsplit] at h; linarith
  have hall : ∀ ψ : Θ, ψ ≠ θ₀ → p ψ a = 0 := by
    intro ψ hψ
    have hmem : ψ ∈ univ.erase θ₀ := Finset.mem_erase.2 ⟨hψ, mem_univ ψ⟩
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _ => (hp x).nonneg a)).1 hzero ψ hmem
  intro θ θ' hne hposθ
  have hθeq : θ = θ₀ := by
    by_contra hc
    exact absurd (hall θ hc) (ne_of_gt hposθ)
  exact hall θ' (by rw [hθeq] at hne; exact fun hcon => hne (hcon ▸ rfl))
