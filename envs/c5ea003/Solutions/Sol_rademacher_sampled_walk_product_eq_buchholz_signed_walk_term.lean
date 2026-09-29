-- Prove2me | solution 1 for rademacher_sampled_walk_product_eq_buchholz_signed_walk_term
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-24T01:33:25.074073+00:00
-- url     : https://prove2.me/submissions/a4c0727f-75c0-4d99-bd71-5425a8afe1b8

import Definitions.Def_buchholz_signed_walk_sum

open MatrixCompletion
open scoped BigOperators

theorem solution
    {n n1 n2 : Nat} (Omega eps : Finset (Fin n1 × Fin n2)) (p : ℝ)
    (X : RealMatrix n1 n2)
    (rows : Fin n → Fin n1) (cols : Fin n → Fin n2) :
    (∏ k : Fin n,
      rademacherSampledMatrix Omega eps p X (rows k) (cols k) *
        rademacherSampledMatrix Omega eps p X
          (rows (buchholzCyclicSucc k)) (cols k))
      =
    buchholzSignedWalkTerm Omega eps p X rows cols := by
  unfold buchholzSignedWalkTerm buchholzWalkProduct buchholzWalkSignMonomial
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  unfold rademacherSampledMatrix
  by_cases hk : (rows k, cols k) ∈ Omega
  · by_cases hsucc : (rows (buchholzCyclicSucc k), cols k) ∈ Omega
    · simp [hk, hsucc]
      ring
    · simp [hk, hsucc]
  · by_cases hsucc : (rows (buchholzCyclicSucc k), cols k) ∈ Omega
    · simp [hk, hsucc]
    · simp [hk, hsucc]
