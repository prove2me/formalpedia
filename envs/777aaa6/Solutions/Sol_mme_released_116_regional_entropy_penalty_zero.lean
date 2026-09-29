-- Prove2me | solution 1 for mme_released_116_regional_entropy_penalty_zero
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T23:49:25.246567+00:00
-- url     : https://prove2.me/submissions/d3f96df2-b1d0-43b2-aaa7-d61dbb866609

import Theorems.Thm_mme_released_116_regional_split_mass
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_recursive_thin_split_data
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

open BigOperators MME MME.RecursiveThinSplit
set_option autoImplicit false

private abbrev Split116 := Split 4 ![1, 1, 6]
private def c004 : Split116 := ⟨![0, 0, 4], by decide⟩
private def c013 : Split116 := ⟨![0, 1, 3], by decide⟩
private def c103 : Split116 := ⟨![1, 0, 3], by decide⟩
private def c112 : Split116 := ⟨![1, 1, 2], by decide⟩

private theorem split_univ : (Finset.univ : Finset Split116) = {c004, c013, c103, c112} := by
  decide

private theorem split_sum (f : Split116 → ℝ) :
    ∑ c, f c = f c004 + f c013 + f c103 + f c112 := by
  rw [split_univ]
  norm_num [c004, c013, c103, c112, add_assoc]

private theorem marginal_sum (f : Split116 → ℝ) (i : Fin 3) (j : Fin 5) :
    mme_modern_marginal (fun c : Split116 => c.val i) f j =
      ∑ c, if c.val i = j then f c else 0 := by
  unfold mme_modern_marginal
  rw [← Finset.sum_subtype (Finset.univ.filter (fun c : Split116 => c.val i = j))
    (fun c => by simp) f, Finset.sum_filter]

/-- The three coordinate marginals determine a distribution on the four
splits of the (1,1,6) component. The extreme third-coordinate entries recover
004 and 112; the first two marginals then recover 103 and 013. -/
private theorem mme_116_split_marginals_injective (alpha rho : Split 4 ![1, 1, 6] → ℝ)
    (h : ∀ (i : Fin 3) (j : Fin 5),
      mme_modern_marginal (fun c : Split 4 ![1, 1, 6] => c.val i) rho j =
        mme_modern_marginal (fun c : Split 4 ![1, 1, 6] => c.val i) alpha j) :
    rho = alpha := by
  have h004 := h 2 4
  have h112 := h 2 2
  have h103 := h 0 1
  have h013 := h 1 1
  simp only [marginal_sum, split_sum] at h004 h112 h103 h013
  change rho c004 + 0 + 0 + 0 = alpha c004 + 0 + 0 + 0 at h004
  change 0 + 0 + 0 + rho c112 = 0 + 0 + 0 + alpha c112 at h112
  change 0 + 0 + rho c103 + rho c112 = 0 + 0 + alpha c103 + alpha c112 at h103
  change 0 + rho c013 + 0 + rho c112 = 0 + alpha c013 + 0 + alpha c112 at h013
  simp only [zero_add, add_zero] at h004 h112 h103 h013
  funext c
  have hc : c ∈ ({c004, c013, c103, c112} : Finset Split116) := by
    rw [← split_univ]
    exact Finset.mem_univ c
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> linarith

/-- Every probability distribution on the splits of (1,1,6) has zero
maximum-entropy penalty because its coordinate marginals fix it uniquely. -/
private theorem mme_116_split_entropy_penalty_zero (alpha : Split 4 ![1, 1, 6] → ℝ)
    (hnonneg : ∀ c, 0 ≤ alpha c) (hmass : ∑ c, alpha c = 1) :
    entropyPenalty alpha = 0 := by
  have hset : SameMarginalDistributions alpha = {alpha} := by
    ext rho
    constructor
    · intro h
      exact Set.mem_singleton_iff.mpr (mme_116_split_marginals_injective alpha rho h.2.2)
    · rintro rfl
      exact ⟨hnonneg, hmass, fun _ _ => rfl⟩
  simp [entropyPenalty, hset]


open scoped Classical

/-- The maximum-entropy penalty vanishes in each of the six released regions. -/
theorem solution (r : Fin 6) :
    entropyPenalty (fun c : Released116.Split =>
      (Released116.splitCount r c : ℝ) / Released116.regionalSize r) = 0 := by
  apply mme_116_split_entropy_penalty_zero
  · intro c
    positivity
  · have hm := (mme_released_116_regional_split_mass r).2
    change (∑ c : Split 4 ![1, 1, 6], Released116.splitCount r c) = _ at hm
    rw [← Finset.sum_div, ← Nat.cast_sum, hm]
    exact div_self (by exact_mod_cast (mme_released_116_regional_split_mass r).1.ne')

/-- The released (1,1,6) regional rate has no aggregate entropy-penalty term. -/
private theorem mme_released_116_penalty_potential_zero :
    RegionRate.penaltyPotential Released116.regionalSize Released116.splitCount = 0 := by
  simp [RegionRate.penaltyPotential, solution]


#print axioms solution
