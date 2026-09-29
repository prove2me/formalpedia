-- Prove2me | solution 1 for E_sign_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-23T21:13:52.228073+00:00
-- url     : https://prove2.me/submissions/59af1530-1732-48eb-afbc-6a8dd857b295

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Ring.Parity

open scoped BigOperators

theorem solution {n1 n2 : Nat} (mult : (Fin n1 × Fin n2) → ℕ) :
    ((1 : ℝ) / 2) ^ Fintype.card (Fin n1 × Fin n2) *
        ∑ eps : Finset (Fin n1 × Fin n2),
          ∏ c : (Fin n1 × Fin n2),
            (if c ∈ eps then (1 : ℝ) else -1) ^ (mult c)
      = if (∀ c, Even (mult c)) then 1 else 0 := by
  classical
  let ι := Fin n1 × Fin n2
  let a : ι → ℝ := fun c => (-1 : ℝ) ^ mult c
  have hterm (eps : Finset ι) :
      (∏ c : ι, (if c ∈ eps then (1 : ℝ) else -1) ^ mult c)
        = ∏ c : ι, if c ∈ eps then (1 : ℝ) else a c := by
    refine Finset.prod_congr rfl ?_
    intro c _
    by_cases hc : c ∈ eps
    · simp [a, hc]
    · simp [a, hc]
  have hsum_if :
      (∑ eps : Finset ι, ∏ c : ι, if c ∈ eps then (1 : ℝ) else a c)
        = ∏ c : ι, (1 + a c) := by
    let U : Finset ι := Finset.univ
    calc
      (∑ eps : Finset ι, ∏ c : ι, if c ∈ eps then (1 : ℝ) else a c)
          = ∑ eps ∈ U.powerset, ∏ c ∈ U, if c ∈ eps then (1 : ℝ) else a c := by
            simp [U]
      _ = ∑ eps ∈ U.powerset, (∏ c ∈ eps, (1 : ℝ)) * ∏ c ∈ U \ eps, a c := by
            refine Finset.sum_congr rfl ?_
            intro eps heps
            have hfilter : U.filter (fun c => c ∈ eps) = eps := by
              ext c
              simp [U]
            have hfilter_not : U.filter (fun c => ¬ c ∈ eps) = U \ eps := by
              ext c
              simp [U, Finset.mem_sdiff]
            rw [Finset.prod_ite]
            simp [hfilter, hfilter_not]
      _ = ∏ c ∈ U, (1 + a c) := by
            simpa using (Finset.prod_add (fun _ : ι => (1 : ℝ)) a U).symm
      _ = ∏ c : ι, (1 + a c) := by
            simp [U]
  have hsum :
      (∑ eps : Finset ι, ∏ c : ι, (if c ∈ eps then (1 : ℝ) else -1) ^ mult c)
        = ∏ c : ι, (1 + a c) := by
    calc
      (∑ eps : Finset ι, ∏ c : ι, (if c ∈ eps then (1 : ℝ) else -1) ^ mult c)
          = ∑ eps : Finset ι, ∏ c : ι, if c ∈ eps then (1 : ℝ) else a c := by
            refine Finset.sum_congr rfl ?_
            intro eps _
            exact hterm eps
      _ = ∏ c : ι, (1 + a c) := hsum_if
  have hE :
      ((1 : ℝ) / 2) ^ Fintype.card ι *
          (∑ eps : Finset ι, ∏ c : ι, (if c ∈ eps then (1 : ℝ) else -1) ^ mult c)
        = ∏ c : ι, ((1 : ℝ) / 2) * (1 + a c) := by
    rw [hsum]
    calc
      ((1 : ℝ) / 2) ^ Fintype.card ι * ∏ c : ι, (1 + a c)
          = (∏ c : ι, ((1 : ℝ) / 2)) * ∏ c : ι, (1 + a c) := by simp
      _ = ∏ c : ι, ((1 : ℝ) / 2) * (1 + a c) := by
            rw [← Finset.prod_mul_distrib]
  rw [hE]
  by_cases hall : ∀ c : ι, Even (mult c)
  · rw [if_pos hall]
    apply Finset.prod_eq_one
    intro c _
    have : a c = 1 := by simp only [a]; rw [Even.neg_one_pow (hall c)]
    rw [this]; norm_num
  · rw [if_neg hall]
    have hex : ∃ c : ι, ¬ Even (mult c) := by
      simpa [not_forall] using hall
    rcases hex with ⟨c, hc⟩
    apply Finset.prod_eq_zero (i := c) (Finset.mem_univ c)
    have : a c = -1 := by
      simp only [a]; rw [(Nat.not_even_iff_odd.mp hc).neg_one_pow]
    rw [this]; norm_num
