-- Prove2me | solution 1 for BookSixth.bregman_minc_claimB
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-17T15:42:53.016466+00:00
-- url     : https://prove2.me/submissions/2d39d5b0-3f52-4f91-9b96-f7f4818f74a4

import Mathlib
import Definitions.Def_BregmanMincWeights
import Theorems.Thm_BookSixth_bregman_minc_geometric_mean

open scoped BigOperators
open BregmanMincWeights

theorem solution (n : ℕ) (A : Matrix (Fin n) (Fin n) ℕ) (hA : ∀ i j, A i j ≤ 1)
    (hrows : ∀ i, 0 < ∑ j, A i j) (σ : Equiv.Perm (Fin n)) (_hσ : σ ∈ aSys A) :
    (n.factorial : ℝ) * ∏ i : Fin n,
      ((Nat.factorial (∑ j, A i j) : ℕ) : ℝ) ^ (-(1 : ℝ) / ((∑ j, A i j : ℕ) : ℝ)) ≤
    ∑ π : Equiv.Perm (Fin n), qW A σ π := by
  classical
  have hfac : (0 : ℝ) < n.factorial := by
    exact_mod_cast Nat.factorial_pos n
  have hnonneg : ∀ π : Equiv.Perm (Fin n), 0 ≤ qW A σ π := by
    intro π
    unfold qW
    exact Finset.prod_nonneg (fun _ _ => div_nonneg (by norm_num) (Nat.cast_nonneg _))
  have hmean := Real.geom_mean_le_arith_mean
    (Finset.univ : Finset (Equiv.Perm (Fin n)))
    (fun _ => (1 : ℝ)) (fun π => qW A σ π)
    (fun _ _ => by norm_num)
    (by simpa [Fintype.card_perm] using hfac)
    (fun π _ => hnonneg π)
  have hbound :
      (∏ π : Equiv.Perm (Fin n), qW A σ π) ^ ((n.factorial : ℝ)⁻¹) ≤
        (∑ π : Equiv.Perm (Fin n), qW A σ π) / (n.factorial : ℝ) := by
    simpa [Fintype.card_perm] using hmean
  rw [BookSixth.bregman_minc_geometric_mean n A hA hrows σ _hσ] at hbound
  have hmul := (le_div_iff₀ hfac).1 hbound
  simpa only [mul_comm] using hmul
