-- Prove2me | solution 1 for mme_complete_split_112_exact_address_MM_dimensions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-06T22:39:41.011619+00:00
-- url     : https://prove2.me/submissions/5e8fd8bd-24b9-4cf3-8696-4d5e91bea087

import Theorems.Thm_mme_complete_split_112_concrete_four_block_certificate
import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_induced_word_zeroing
import Theorems.Thm_mme_kronFin_MMObj_iso
import Theorems.Thm_mme_kronFin_respects_iso
import Mathlib.Tactic

open MME MME.CompleteSplit112 BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem supported_eq_one_of_four
    {sigma : Fin 3 → Fin 3}
    (hsigma :
      (sigma 0 = 0 ∧ sigma 1 = 0 ∧ sigma 2 = 0) ∨
      (sigma 0 = 1 ∧ sigma 1 = 1 ∧ sigma 2 = 1) ∨
      (sigma 0 = 0 ∧ sigma 1 = 1 ∧ sigma 2 = 2) ∨
      (sigma 0 = 1 ∧ sigma 1 = 0 ∧ sigma 2 = 2)) :
    sigma = ![0, 0, 0] ∨ sigma = ![1, 1, 1] ∨
      sigma = ![0, 1, 2] ∨ sigma = ![1, 0, 2] := by
  rcases hsigma with h | h | h | h
  · left
    funext i
    fin_cases i <;> simp_all
  · right; left
    funext i
    fin_cases i <;> simp_all
  · right; right; left
    funext i
    fin_cases i <;> simp_all
  · right; right; right
    funext i
    fin_cases i <;> simp_all

private theorem supported_block_iso
    {K : Type u} [Field K] (q : ℕ)
    (sigma : Fin 3 → Fin 3)
    (hsigma :
      (sigma 0 = 0 ∧ sigma 1 = 0 ∧ sigma 2 = 0) ∨
      (sigma 0 = 1 ∧ sigma 1 = 1 ∧ sigma 2 = 1) ∨
      (sigma 0 = 0 ∧ sigma 1 = 1 ∧ sigma 2 = 2) ∨
      (sigma 0 = 1 ∧ sigma 1 = 0 ∧ sigma 2 = 2)) :
    TensorObj.Isomorphic
      (MMObj K (if sigma 2 = 2 then q else 1)
        (if sigma 2 = 2 then 1 else q) (if sigma 2 = 2 then q else 1))
      ((grading K q).blockSubtensor sigma) := by
  have hb := mme_complete_split_112_concrete_four_block_certificate (K := K) q
  rcases supported_eq_one_of_four hsigma with rfl | rfl | rfl | rfl
  · simpa using hb.2.1
  · simpa using hb.2.2.1
  · simpa using hb.2.2.2.1
  · simpa using hb.2.2.2.2

private theorem prod_if_eq
    (q R : ℕ) (f : Fin R → Fin 3) (r : Fin 3) :
    (∏ j : Fin R, if f j = r then q else 1) =
      q ^ (Finset.univ.filter (fun j : Fin R ↦ f j = r)).card := by
  classical
  rw [← Finset.prod_filter]
  simp

/-- Exact three dimensions of every retained address component for the
literal coupled grading, not only its matrix-multiplication volume. -/
theorem solution
    {K : Type u} [Field K] (q N L G : ℕ)
    (address : CWQ6ExactCoupledAddress N L G) :
    TensorObj.Isomorphic
      (MMObj K (q ^ (2 * G)) (q ^ (2 * L)) (q ^ (2 * G)))
      (gradedAddressBlock (grading K q) address.1) := by
  classical
  let zword : Fin (2 * N) → Fin 3 := fun j ↦ address.1 2 j
  let a : Fin (2 * N) → ℕ := fun j ↦ if zword j = 2 then q else 1
  let b : Fin (2 * N) → ℕ := fun j ↦ if zword j = 2 then 1 else q
  have hpoint : ∀ j : Fin (2 * N),
      TensorObj.Isomorphic (MMObj K (a j) (b j) (a j))
        ((grading K q).blockSubtensor (cwQ6CoupledAddressType address.1 j)) := by
    intro j
    exact supported_block_iso q _ (address.2.1 j)
  have hfamily := mme_kronFin_respects_iso (2 * N)
    (fun j ↦ MMObj K (a j) (b j) (a j))
    (fun j ↦ (grading K q).blockSubtensor (cwQ6CoupledAddressType address.1 j))
    hpoint
  have hMM := mme_kronFin_MMObj_iso (K := K) (2 * N) a b a
  have hiso := hMM.symm.trans hfamily
  have hzcount (r : Fin 3) :
      (Finset.univ.filter (fun j : Fin (2 * N) ↦ zword j = r)).card =
        cwQ6CoupledMarginalMultiplicity N L G 2 r := address.2.2 2 r
  have ha : (∏ j, a j) = q ^ (2 * G) := by
    change (∏ j : Fin (2 * N), if zword j = 2 then q else 1) = _
    rw [prod_if_eq, hzcount 2]
    simp [cwQ6CoupledMarginalMultiplicity]
  have hbpoint (j : Fin (2 * N)) :
      b j = (if zword j = 0 then q else 1) *
        (if zword j = 1 then q else 1) := by
    change (if zword j = 2 then 1 else q) = _
    generalize zword j = z
    fin_cases z <;> simp
  have hb : (∏ j, b j) = q ^ (2 * L) := by
    simp_rw [hbpoint, Finset.prod_mul_distrib]
    rw [prod_if_eq, prod_if_eq, hzcount 0, hzcount 1]
    simp [cwQ6CoupledMarginalMultiplicity, ← pow_add, two_mul]
  rw [ha, hb] at hiso
  exact hiso
