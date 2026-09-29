-- Prove2me | solution 1 for mme_common_hash_scale_real_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T21:18:47.855463+00:00
-- url     : https://prove2.me/submissions/0e120e5c-8b4c-4ae5-a331-882c98a70a5b

import Definitions.Def_mme_common_hash_scale
import Mathlib
open BigOperators MME.RegionRealization
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem solution {J : Type*} [Fintype J] (grade : ℕ) (num den : J → ℕ)
    (M : ℝ) (hM : 0 ≤ M) (hload : ∀ j, (num j : ℝ) ≤ M * den j) :
    (commonScale grade num den : ℝ) ≤ (grade : ℝ) + 2 + M := by
  classical
  have hq (j : J) : ((num j / den j + 1 : ℕ) : ℝ) ≤ M + 1 := by
    by_cases hz : den j = 0
    · simp [hz,hM]
    · have hd : 0 < (den j : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hz
      have hdiv : ((num j / den j : ℕ) : ℝ) ≤ (num j : ℝ) / den j := Nat.cast_div_le
      have hm := (div_le_iff₀ hd).mpr (hload j)
      simp only [Nat.cast_add,Nat.cast_one]
      linarith
  have hs : ((Finset.univ.sup (fun j ↦ num j / den j + 1) : ℕ) : ℝ) ≤ M + 1 := by
    by_cases hJ : Nonempty J
    · letI := hJ
      obtain ⟨j,hj,hmax⟩ := Finset.exists_mem_eq_sup (s := (Finset.univ : Finset J))
        (f := fun j ↦ num j / den j + 1) Finset.univ_nonempty
      rw [hmax]
      exact hq j
    · haveI : IsEmpty J := not_nonempty_iff.mp hJ
      simp
      linarith
  unfold commonScale
  rw [Nat.cast_max,Nat.cast_add,Nat.cast_one]
  apply max_le
  · linarith
  · linarith [show (0 : ℝ) ≤ (grade : ℝ) from Nat.cast_nonneg grade]
