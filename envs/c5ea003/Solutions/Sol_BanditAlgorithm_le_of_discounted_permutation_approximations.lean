-- Prove2me | solution 1 for BanditAlgorithm.le_of_discounted_permutation_approximations
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T03:41:08.921112+00:00
-- url     : https://prove2.me/submissions/c910c55e-7f73-4751-9bdc-b9a945901f20

import Theorems.Thm_BanditAlgorithm_discounted_list_value_le_of_perm_pairwise

open BanditAlgorithm

theorem solution
    {α u v : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hcert : ∀ ε : ℝ, 0 < ε →
      ∃ xs ys : List ℝ,
        xs.Perm ys ∧ ys.Pairwise (· ≥ ·) ∧
        u ≤ xs.foldr (fun z acc ↦ z + α * acc) 0 + ε ∧
        ys.foldr (fun z acc ↦ z + α * acc) 0 ≤ v + ε) :
    u ≤ v := by
  by_contra huv
  have hvu : v < u := lt_of_not_ge huv
  let ε : ℝ := (u - v) / 4
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  obtain ⟨xs, ys, hperm, hsorted, huxs, hysv⟩ := hcert ε hε
  have hxsys :
      xs.foldr (fun z acc ↦ z + α * acc) 0 ≤
        ys.foldr (fun z acc ↦ z + α * acc) 0 :=
    discounted_list_value_le_of_perm_pairwise hα0 hα1 hperm hsorted
  dsimp [ε] at huxs hysv
  linarith
