-- Prove2me | solution 2 for PowerSumSharpness.powerSum_determined_of_gap
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T04:45:47.578919+00:00
-- url     : https://prove2.me/submissions/733b38d6-ee58-47c2-ac2c-43da9f53fb28

import Mathlib
import Definitions.Def_Probability_PowerSumSharpness
open PowerSumSharpness Finset Polynomial in
theorem solution {N : ℕ} {w v : ℕ → ℝ}
    (h : ∀ k ≤ N, powerSum N w k = powerSum N v k) : ∀ i ≤ N, w i = v i := by
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
  exact hdet h
