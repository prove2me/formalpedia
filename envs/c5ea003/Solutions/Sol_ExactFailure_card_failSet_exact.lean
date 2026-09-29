-- Prove2me | solution 1 for ExactFailure.card_failSet_exact
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T06:34:58.476463+00:00
-- url     : https://prove2.me/submissions/0c413278-e7eb-4a59-af1d-8e99aa7f093b

import Mathlib
import Definitions.Def_Geometry_AlmostLosslessDecoder
import Definitions.Def_Geometry_ExactFailureMarginal
open ExactFailure Finset AlmostLossless in
theorem solution {M : ℕ} {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α) (x : α) :
    M ^ (S.erase x).card * (failSet S x M).card
        + (M - 1) ^ (S.erase x).card * M ^ Fintype.card α
      = M ^ (S.erase x).card * M ^ Fintype.card α := by
  classical
  set T := S.erase x with hTdef
  set k := T.card with hk
  set n := Fintype.card α with hn
  have hxT : x ∉ T := notMem_erase x S
  have hkn : k + 1 ≤ n := by
    have : (insert x T).card = k + 1 := card_insert_of_notMem hxT
    rw [← this]
    exact card_le_univ _
  -- codebooks with `H x = c` that avoid `c` on `T`: a product set
  have hfib : ∀ c : Fin M, (univ.filter (fun H : α → Fin M => H x = c ∧ ∀ y ∈ T, H y ≠ c)).card
      = (M - 1) ^ k * M ^ (n - k - 1) := by
    intro c
    have hset : univ.filter (fun H : α → Fin M => H x = c ∧ ∀ y ∈ T, H y ≠ c)
        = Fintype.piFinset (fun i => if i ∈ T then univ.erase c else if i = x then {c} else univ) := by
      ext H
      simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
      constructor
      · rintro ⟨hx, hT⟩ i
        split_ifs with hiT hix
        · exact mem_erase.mpr ⟨hT i hiT, mem_univ _⟩
        · rw [hix, hx]
          exact mem_singleton_self _
        · exact mem_univ _
      · intro h
        refine ⟨?_, fun y hy => ?_⟩
        · have := h x
          rw [if_neg hxT, if_pos rfl] at this
          exact mem_singleton.mp this
        · have := h y
          rw [if_pos hy] at this
          exact (mem_erase.mp this).1
    rw [hset, Fintype.card_piFinset]
    have hsz : ∀ i, (if i ∈ T then univ.erase c else if i = x then {c} else univ).card
        = if i ∈ T then M - 1 else if i = x then 1 else M := by
      intro i
      split_ifs <;> simp [card_erase_of_mem]
    rw [prod_congr rfl (fun i _ => hsz i), prod_ite, prod_const, prod_ite, prod_const,
      prod_const, one_pow, one_mul]
    congr 2
    · rw [filter_mem_eq_inter, univ_inter]
    · have : ((univ.filter (fun i => i ∉ T)).filter (fun i => ¬ i = x)) = univ \ insert x T := by
        ext i
        simp only [mem_filter, mem_univ, true_and, mem_sdiff, mem_insert, not_or]
        tauto
      rw [this, card_sdiff_of_subset (subset_univ _), card_univ, card_insert_of_notMem hxT]
      omega
  -- summing the fibres over the value `c = H x`
  have hcomp : (univ.filter (fun H : α → Fin M => ∀ y ∈ T, H y ≠ H x)).card
      = M * ((M - 1) ^ k * M ^ (n - k - 1)) := by
    rw [card_eq_sum_card_fiberwise (f := fun H : α → Fin M => H x) (t := univ)
      (fun _ _ => mem_univ _)]
    have hf : ∀ c : Fin M, ((univ.filter (fun H : α → Fin M => ∀ y ∈ T, H y ≠ H x)).filter
        (fun H => H x = c)).card = (M - 1) ^ k * M ^ (n - k - 1) := by
      intro c
      rw [filter_filter, ← hfib c]
      congr 1
      ext H
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h2, fun y hy => h2 ▸ h1 y hy⟩
      · rintro ⟨h1, h2⟩
        exact ⟨fun y hy => h1 ▸ h2 y hy, h1⟩
    rw [sum_congr rfl (fun c _ => hf c), sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
  -- the failure set is the complement
  have hfail : failSet S x M = univ \ univ.filter (fun H : α → Fin M => ∀ y ∈ T, H y ≠ H x) := by
    ext H
    simp only [failSet, mem_filter, mem_univ, true_and, mem_sdiff, not_forall, not_not, exists_prop]
    rfl
  have hsum : (failSet S x M).card + M * ((M - 1) ^ k * M ^ (n - k - 1)) = M ^ n := by
    rw [hfail, ← hcomp, card_sdiff_add_card_eq_card (subset_univ _), card_univ, Fintype.card_fun,
      Fintype.card_fin]
  -- multiply the complement count by `M^k`
  have hp : M ^ k * M * M ^ (n - k - 1) = M ^ n := by
    rw [← pow_succ, ← pow_add]
    congr 1
    omega
  calc M ^ k * (failSet S x M).card + (M - 1) ^ k * M ^ n
      = M ^ k * (failSet S x M).card + M ^ k * (M * ((M - 1) ^ k * M ^ (n - k - 1))) := by
        rw [← hp]
        ring
    _ = M ^ k * M ^ n := by rw [← mul_add, hsum]
