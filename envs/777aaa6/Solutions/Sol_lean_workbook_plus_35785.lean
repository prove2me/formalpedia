-- Prove2me | solution 1 for lean_workbook_plus_35785
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:57:30.687369+00:00
-- url     : https://prove2.me/submissions/1488cc97-5f9c-4582-b91d-0aff408eb996

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

private lemma count_multiples (N d : ℕ) :
    ((Finset.Icc 1 N).filter (fun x => d ∣ x)).card = N / d := by
  have hinterval : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hinterval]
  exact Nat.Ioc_filter_dvd_card_eq_div N d

private lemma count_either (N a b : ℕ) :
    ((Finset.Icc 1 N).filter (fun x => a ∣ x ∨ b ∣ x)).card =
      N / a + N / b - N / Nat.lcm a b := by
  have h := Finset.card_union_add_card_inter
    ((Finset.Icc 1 N).filter (fun x => a ∣ x))
    ((Finset.Icc 1 N).filter (fun x => b ∣ x))
  rw [← Finset.filter_or, ← Finset.filter_and] at h
  simp_rw [← Nat.lcm_dvd_iff] at h
  rw [count_multiples, count_multiples, count_multiples] at h
  omega

theorem solution :
    Finset.card (Finset.filter (fun x => 4 ∣ x ∨ 6 ∣ x) (Finset.Icc 1 1000)) -
      Finset.card (Finset.filter (fun x => 24 ∣ x) (Finset.Icc 1 1000)) = 292 := by
  rw [count_either, count_multiples]
  norm_num
