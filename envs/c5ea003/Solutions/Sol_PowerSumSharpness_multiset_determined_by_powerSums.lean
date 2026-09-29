-- Prove2me | solution 1 for PowerSumSharpness.multiset_determined_by_powerSums
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T04:36:46.943345+00:00
-- url     : https://prove2.me/submissions/9a423837-1337-45e6-8e4a-767608063ea9

import Mathlib
import Definitions.Def_Probability_PowerSumSharpness
open PowerSumSharpness Finset Polynomial in
theorem solution {N : ℕ} {s t : Multiset ℕ}
    (hs : ∀ x ∈ s, x ≤ N) (ht : ∀ x ∈ t, x ≤ N)
    (h : ∀ k ≤ N, (s.map (fun x => x ^ k)).sum = (t.map (fun x => x ^ k)).sum) : s = t := by
  classical
  have hdet : ∀ {M : ℕ} {a b : ℕ → ℝ}, (∀ k ≤ M, powerSum M a k = powerSum M b k) →
      ∀ i ≤ M, a i = b i := by
    intro M a b h j hj
    classical
    have key : ∀ p : ℝ[X], p.natDegree ≤ M →
        ∑ i ∈ Finset.range (M + 1), a i * p.eval (i : ℝ)
          = ∑ i ∈ Finset.range (M + 1), b i * p.eval (i : ℝ) := by
      intro p hp
      have hexp : ∀ u : ℕ → ℝ, ∑ i ∈ Finset.range (M + 1), u i * p.eval (i : ℝ)
          = ∑ k ∈ Finset.range (M + 1), p.coeff k * powerSum M u k := by
        intro u
        have e1 : ∀ i : ℕ, u i * p.eval (i : ℝ)
            = ∑ k ∈ Finset.range (M + 1), u i * (p.coeff k * (i : ℝ) ^ k) := by
          intro i
          rw [Polynomial.eval_eq_sum_range' (by omega : p.natDegree < M + 1), Finset.mul_sum]
        rw [Finset.sum_congr rfl (fun i _ => e1 i), Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        simp only [powerSum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => by ring)
      rw [hexp a, hexp b]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [h k (Finset.mem_range_succ_iff.mp hk)]
    have hinj : Set.InjOn (fun i : ℕ => (i : ℝ)) ↑(Finset.range (M + 1)) := by
      intro x _ y _ hxy
      exact Nat.cast_injective hxy
    have hjs : j ∈ Finset.range (M + 1) := Finset.mem_range_succ_iff.mpr hj
    have hdeg : (Lagrange.basis (Finset.range (M + 1)) (fun i : ℕ => (i : ℝ)) j).natDegree ≤ M := by
      refine Polynomial.natDegree_le_iff_degree_le.mpr ?_
      rw [Lagrange.degree_basis hinj hjs, Finset.card_range]
      simp
    have heval : ∀ i ∈ Finset.range (M + 1),
        (Lagrange.basis (Finset.range (M + 1)) (fun i : ℕ => (i : ℝ)) j).eval (i : ℝ)
          = if i = j then 1 else 0 := by
      intro i hi
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl]
        exact Lagrange.eval_basis_self hinj hjs
      · rw [if_neg hij]
        exact Lagrange.eval_basis_of_ne (Ne.symm hij) hi
    have hcollapse : ∀ u : ℕ → ℝ,
        ∑ i ∈ Finset.range (M + 1),
            u i * (Lagrange.basis (Finset.range (M + 1)) (fun i : ℕ => (i : ℝ)) j).eval (i : ℝ)
          = u j := by
      intro u
      have e : ∑ i ∈ Finset.range (M + 1),
            u i * (Lagrange.basis (Finset.range (M + 1)) (fun i : ℕ => (i : ℝ)) j).eval (i : ℝ)
          = ∑ i ∈ Finset.range (M + 1), if i = j then u i else 0 := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [heval i hi]
        by_cases hij : i = j <;> simp [hij]
      rw [e, Finset.sum_ite_eq' (Finset.range (M + 1)) j u, if_pos hjs]
    have h1 := key _ hdeg
    rw [hcollapse a, hcollapse b] at h1
    exact h1
  have hbridge : ∀ (u : Multiset ℕ), (∀ x ∈ u, x ≤ N) → ∀ k : ℕ,
      (((u.map (fun x => x ^ k)).sum : ℕ) : ℝ)
        = powerSum N (fun i => (Multiset.count i u : ℝ)) k := by
    intro u hu k
    rw [Finset.sum_multiset_map_count]
    unfold powerSum
    rw [← Finset.sum_subset (s₁ := u.toFinset) (s₂ := Finset.range (N + 1))]
    · push_cast [smul_eq_mul]
      refine Finset.sum_congr rfl (fun m _ => by ring)
    · intro m hm
      exact Finset.mem_range_succ_iff.mpr (hu m (Multiset.mem_toFinset.mp hm))
    · intro m _ hm
      have h0 : Multiset.count m u = 0 := by
        rw [Multiset.count_eq_zero]
        intro hmem
        exact hm (Multiset.mem_toFinset.mpr hmem)
      simp [h0]
  have hps : ∀ k ≤ N, powerSum N (fun i => (Multiset.count i s : ℝ)) k
      = powerSum N (fun i => (Multiset.count i t : ℝ)) k := by
    intro k hk
    rw [← hbridge s hs k, ← hbridge t ht k, h k hk]
  have hcount : ∀ i ≤ N, Multiset.count i s = Multiset.count i t := by
    intro i hi
    have := hdet hps i hi
    exact_mod_cast this
  refine Multiset.ext.mpr (fun a => ?_)
  by_cases ha : a ≤ N
  · exact hcount a ha
  · have h1 : Multiset.count a s = 0 := by
      rw [Multiset.count_eq_zero]
      intro hmem
      exact ha (hs a hmem)
    have h2 : Multiset.count a t = 0 := by
      rw [Multiset.count_eq_zero]
      intro hmem
      exact ha (ht a hmem)
    rw [h1, h2]
