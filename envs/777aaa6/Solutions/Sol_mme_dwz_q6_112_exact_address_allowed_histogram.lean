-- Prove2me | solution 1 for mme_dwz_q6_112_exact_address_allowed_histogram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T13:54:32.593327+00:00
-- url     : https://prove2.me/submissions/703ba668-b517-448d-9c3c-b2eafcd635fd

import Mathlib.Tactic
import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_q6_112_exact_profile_data

open MME

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ)
    (address : CWQ6ExactCoupledAddress
      (50000000 * (20088623 * m))
      (21015 * (20088623 * m))
      (49978985 * (20088623 * m))) :
    (2 * (50000000 * (20088623 * m)) =
      MME.DWZTable2Counts.component (12 : Fin 15) * m) ∧
    ∀ a : Fin 3,
      Fintype.card
          {r : Fin (2 * (50000000 * (20088623 * m))) //
            mme_dwz_q6_coupled_Z_leftGrade (address.1 2 r) = a} =
        MME.DWZTable2Counts.split (12 : Fin 15) a * m := by
  constructor
  · simp [MME.DWZTable2Counts.component]
    ring
  · intro a
    fin_cases a
    · have h := address.2.2 2 (1 : Fin 3)
      rw [Fintype.card_subtype]
      change (Finset.univ.filter (fun r ↦
        mme_dwz_q6_coupled_Z_leftGrade (address.1 2 r) = 0)).card =
          422162412345 * m
      have hfilter :
          Finset.univ.filter (fun r ↦
              mme_dwz_q6_coupled_Z_leftGrade (address.1 2 r) = 0) =
            Finset.univ.filter (fun r ↦ address.1 2 r = 1) := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        generalize hz : address.1 2 r = z
        fin_cases z <;> simp [mme_dwz_q6_coupled_Z_leftGrade]
      rw [hfilter]
      change (Finset.univ.filter (fun j ↦ address.1 2 j = 1)).card =
        21015 * (20088623 * m) at h
      convert h using 1
      all_goals ring
    · have h := address.2.2 2 (2 : Fin 3)
      rw [Fintype.card_subtype]
      change (Finset.univ.filter (fun r ↦
        mme_dwz_q6_coupled_Z_leftGrade (address.1 2 r) = 1)).card =
          2008017975175310 * m
      have hfilter :
          Finset.univ.filter (fun r ↦
              mme_dwz_q6_coupled_Z_leftGrade (address.1 2 r) = 1) =
            Finset.univ.filter (fun r ↦ address.1 2 r = 2) := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        generalize hz : address.1 2 r = z
        fin_cases z <;> simp [mme_dwz_q6_coupled_Z_leftGrade]
      rw [hfilter]
      change (Finset.univ.filter (fun j ↦ address.1 2 j = 2)).card =
        2 * (49978985 * (20088623 * m)) at h
      convert h using 1
      all_goals ring
    · have h := address.2.2 2 (0 : Fin 3)
      rw [Fintype.card_subtype]
      change (Finset.univ.filter (fun r ↦
        mme_dwz_q6_coupled_Z_leftGrade (address.1 2 r) = 2)).card =
          422162412345 * m
      have hfilter :
          Finset.univ.filter (fun r ↦
              mme_dwz_q6_coupled_Z_leftGrade (address.1 2 r) = 2) =
            Finset.univ.filter (fun r ↦ address.1 2 r = 0) := by
        ext r
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        generalize hz : address.1 2 r = z
        fin_cases z <;> simp [mme_dwz_q6_coupled_Z_leftGrade]
      rw [hfilter]
      change (Finset.univ.filter (fun j ↦ address.1 2 j = 0)).card =
        21015 * (20088623 * m) at h
      convert h using 1
      all_goals ring
