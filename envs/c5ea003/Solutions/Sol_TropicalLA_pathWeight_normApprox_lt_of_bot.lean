-- Prove2me | solution 1 for TropicalLA.pathWeight_normApprox_lt_of_bot
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T10:20:53.423277+00:00
-- url     : https://prove2.me/submissions/ec1f7525-e185-43a7-97d7-bc375b3de732

import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalIrreducible
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalReducible

open Finset TropicalLA in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {A : Matrix ι ι (WithBot ℝ)} {lam : ℝ}
    {p : ℕ → ι} {m t : ℕ} (hmn : m ≤ Fintype.card ι) (ht : t < m)
    (hbot : A (p t) (p (t + 1)) = ⊥) :
    pathWeight (normApprox A lam) p m < -((Fintype.card ι : ℝ) * spreadAbs A lam) := by
  classical
  have hS1 : 1 ≤ spreadAbs A lam := by
    unfold spreadAbs
    have := abs_nonneg (entryMax A)
    have := abs_nonneg (entryMin A)
    have := abs_nonneg lam
    linarith
  have hn0 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hpen : 0 ≤ 2 * (Fintype.card ι : ℝ) * spreadAbs A lam :=
    mul_nonneg (mul_nonneg (by norm_num) hn0) (by linarith)
  -- every entry of the penalised matrix is at most `spreadAbs`
  have hedge : ∀ i j, normApprox A lam i j ≤ spreadAbs A lam := by
    intro i j
    unfold normApprox
    split_ifs with h
    · unfold penaltyN
      linarith
    · have h1 : finPart A i j ≤ entryMax A := by
        unfold entryMax
        exact Finset.le_sup' (fun q : ι × ι => finPart A q.1 q.2) (mem_univ (i, j))
      have h2 := le_abs_self (entryMax A)
      have h3 : -lam ≤ |lam| := by
        rw [← abs_neg]
        exact le_abs_self _
      have h4 := abs_nonneg (entryMin A)
      have h5 := abs_nonneg lam
      unfold spreadAbs
      linarith
  have hbotv : normApprox A lam (p t) (p (t + 1)) = -penaltyN A lam := by
    unfold normApprox
    rw [if_pos hbot]
  have hsplit := Finset.add_sum_erase (range m) (fun s => normApprox A lam (p s) (p (s + 1)))
    (Finset.mem_range.2 ht)
  have hrest : ∑ s ∈ (range m).erase t, normApprox A lam (p s) (p (s + 1))
      ≤ ((m : ℝ) - 1) * spreadAbs A lam := by
    have h := Finset.sum_le_card_nsmul ((range m).erase t)
      (fun s => normApprox A lam (p s) (p (s + 1))) (spreadAbs A lam) (fun s _ => hedge _ _)
    rw [Finset.card_erase_of_mem (Finset.mem_range.2 ht), Finset.card_range, nsmul_eq_mul] at h
    have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      simp
    rw [hm1] at h
    exact h
  have hmn' : (m : ℝ) ≤ Fintype.card ι := by exact_mod_cast hmn
  have hmS := mul_le_mul_of_nonneg_right hmn' (by linarith : (0 : ℝ) ≤ spreadAbs A lam)
  unfold pathWeight
  rw [← hsplit]
  beta_reduce
  rw [hbotv]
  unfold penaltyN
  linarith
