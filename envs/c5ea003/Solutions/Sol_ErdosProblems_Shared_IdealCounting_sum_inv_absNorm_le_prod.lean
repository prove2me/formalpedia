-- Prove2me | solution 1 for ErdosProblems.Shared.IdealCounting.sum_inv_absNorm_le_prod
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:28:34.280634+00:00
-- url     : https://prove2.me/submissions/36773d48-de77-417d-b20a-06bf032d6644

import Definitions.Def_ErdosProblems_Shared_IdealCountingEuler
import Mathlib.Analysis.PSeries
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Ideal.Int

/-!
# Counting ideals by their prime factors in a number field

For a number field `K` and a predicate `P` on ideals of `𝓞 K`, `countSupp K P n` is the
number of ideals of absolute norm `n` all of whose prime factors satisfy `P`.  This file
proves the three coefficientwise facts that feed the pole comparison of
`ErdosProblems.Shared.DirichletPole`:

* `card_le_sum_countSupp` (**factorisation into two parts**): every ideal of norm `n` is the
  product of its `P`-part and its `¬P`-part, so the number of ideals of norm `n` is at most the
  Dirichlet convolution of the two restricted counts;
* `sum_countSupp_div_le` (**the bad part converges at `s = 1`**): when `P 𝔭` says that the
  norm of `𝔭` is a prime larger than `N₀`, the series `∑ countSupp K (¬P) n / n` has bounded
  partial sums.  The primes excluded are finitely many primes of small norm and primes of
  norm `p ^ f` with `f ≥ 2`; at most `[K : ℚ]` primes lie over each `p`, so their
  reciprocal norms are dominated by `[K : ℚ] ∑ 1 / p²`, and a finite Euler product over the
  primes involved bounds the whole series;
* `sum_countSupp_mul_le` (**split primes double the count**): if every prime `𝔭` with `P 𝔭`
  has two distinct primes of an extension `M` above it, each of the same norm as `𝔭`, then
  the Dirichlet convolution of the `P`-count with itself is at most the number of ideals of
  `𝓞 M` of norm `n`.  The injection sends a pair of ideals `(I, J)` to the product of the
  first lifts of the prime factors of `I` and the second lifts of those of `J`.
-/

noncomputable section

namespace ErdosProblems.Shared.IdealCounting
open NumberField UniqueFactorizationMonoid Ideal

variable (K : Type*) [Field K] [NumberField K]





variable {K}











/-! ### Factorisation into a `P`-part and a `¬P`-part -/







/-! ### Split primes: the convolution of the `P`-count with itself -/



/-! ### A finite Euler product bound -/
end ErdosProblems.Shared.IdealCounting

open NumberField UniqueFactorizationMonoid Ideal
variable (K : Type*) [Field K] [NumberField K]
variable {K}
open ErdosProblems in
open ErdosProblems.Shared in
open ErdosProblems.Shared.IdealCounting in
theorem solution (F : Finset (Ideal (𝓞 K))) (hF : ∀ 𝔭 ∈ F, 2 ≤ absNorm 𝔭)
    (T : Finset (Ideal (𝓞 K)))
    (hT : ∀ I ∈ T, I ≠ ⊥ ∧ ∀ 𝔭 ∈ normalizedFactors I, 𝔭 ∈ F) :
    ∑ I ∈ T, ((absNorm I : ℝ))⁻¹ ≤ ∏ 𝔭 ∈ F, (1 - ((absNorm 𝔭 : ℝ))⁻¹)⁻¹ := by
  classical
  set E : ℕ := T.sup (fun I => Multiset.card (normalizedFactors I)) with hE
  let Φ : (F → ℕ) → Ideal (𝓞 K) := fun e => ∏ i : F, (i : Ideal (𝓞 K)) ^ (e i)
  have hsub : T ⊆ (Fintype.piFinset (fun _ : F => Finset.range (E + 1))).image Φ := by
    intro I hI
    obtain ⟨hI0, hIF⟩ := hT I hI
    rw [Finset.mem_image]
    refine ⟨fun i => Multiset.count (i : Ideal (𝓞 K)) (normalizedFactors I), ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_range, Nat.lt_succ_iff]
      exact (Multiset.count_le_card _ _).trans
        (Finset.le_sup (f := fun I => Multiset.card (normalizedFactors I)) hI)
    · simp only [Φ]
      rw [Finset.prod_coe_sort F (fun i => i ^ Multiset.count i (normalizedFactors I)),
        ← Finset.prod_multiset_count_of_subset (normalizedFactors I) F]
      · exact Ideal.prod_normalizedFactors_eq_self hI0
      · intro 𝔭 h𝔭
        exact hIF 𝔭 (Multiset.mem_toFinset.mp h𝔭)
  have hw : ∀ e : F → ℕ, ((absNorm (Φ e) : ℝ))⁻¹ =
      ∏ i : F, (((absNorm (i : Ideal (𝓞 K)) : ℝ))⁻¹) ^ (e i) := by
    intro e
    simp only [Φ, map_prod, map_pow, Nat.cast_prod, Nat.cast_pow, Finset.prod_inv_distrib,
      inv_pow]
  have hnn : ∀ I : Ideal (𝓞 K), 0 ≤ ((absNorm I : ℝ))⁻¹ := fun I =>
    inv_nonneg.mpr (Nat.cast_nonneg _)
  calc ∑ I ∈ T, ((absNorm I : ℝ))⁻¹
      ≤ ∑ I ∈ (Fintype.piFinset (fun _ : F => Finset.range (E + 1))).image Φ,
          ((absNorm I : ℝ))⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun I _ _ => hnn I)
    _ ≤ ∑ e ∈ Fintype.piFinset (fun _ : F => Finset.range (E + 1)),
          ((absNorm (Φ e) : ℝ))⁻¹ :=
        Finset.sum_image_le_of_nonneg (fun I _ => hnn I)
    _ = ∑ e ∈ Fintype.piFinset (fun _ : F => Finset.range (E + 1)),
          ∏ i : F, (((absNorm (i : Ideal (𝓞 K)) : ℝ))⁻¹) ^ (e i) :=
        Finset.sum_congr rfl fun e _ => hw e
    _ = ∏ i : F, ∑ k ∈ Finset.range (E + 1), (((absNorm (i : Ideal (𝓞 K)) : ℝ))⁻¹) ^ k :=
        (Finset.prod_univ_sum (ι := F) (fun _ => Finset.range (E + 1))
          (fun (i : F) (k : ℕ) => (((absNorm (i : Ideal (𝓞 K)) : ℝ))⁻¹) ^ k)).symm
    _ ≤ ∏ i : F, (1 - ((absNorm (i : Ideal (𝓞 K)) : ℝ))⁻¹)⁻¹ := by
        apply Finset.prod_le_prod
        · intro i _
          exact Finset.sum_nonneg fun k _ => pow_nonneg (hnn _) k
        · intro i _
          have h2 : (2 : ℝ) ≤ absNorm (i : Ideal (𝓞 K)) := by exact_mod_cast hF i i.2
          have hx0 : 0 ≤ ((absNorm (i : Ideal (𝓞 K)) : ℝ))⁻¹ := hnn _
          have hx1 : ((absNorm (i : Ideal (𝓞 K)) : ℝ))⁻¹ < 1 :=
            inv_lt_one_of_one_lt₀ (by linarith)
          rw [← tsum_geometric_of_lt_one hx0 hx1]
          exact Summable.sum_le_tsum _ (fun k _ => pow_nonneg hx0 k)
            (summable_geometric_of_lt_one hx0 hx1)
    _ = ∏ 𝔭 ∈ F, (1 - ((absNorm 𝔭 : ℝ))⁻¹)⁻¹ :=
        Finset.prod_coe_sort F (fun 𝔭 => (1 - ((absNorm 𝔭 : ℝ))⁻¹)⁻¹)
