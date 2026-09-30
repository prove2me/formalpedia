-- Prove2me | solution 1 for lean_workbook_plus_61377
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:33:44.728371+00:00
-- url     : https://prove2.me/submissions/4a057efd-7fc8-4b36-afb6-412f483cff6c

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

private def nextResidue (b : ℕ) : ℕ := 2 * b % 11

private lemma next_mem (b : ℕ) (hb : b ∈ Finset.Icc 1 10) :
    nextResidue b ∈ Finset.Icc 1 10 := by
  have cert : ∀ b : Fin 11, 0 < b.val → nextResidue b.val ∈ Finset.Icc 1 10 := by
    decide
  have h := Finset.mem_Icc.mp hb
  exact cert ⟨b, by omega⟩ h.1

private lemma orbit_hits (a b : ℕ) (ha : a ∈ Finset.Icc 1 10)
    (hb : b ∈ Finset.Icc 1 10) : ∃ k : ℕ, nextResidue^[k] b = a := by
  have cert : ∀ a b : Fin 11, 0 < a.val → 0 < b.val →
      ∃ k : Fin 10, nextResidue^[k.val] b.val = a.val := by
    decide
  have ha' := Finset.mem_Icc.mp ha
  have hb' := Finset.mem_Icc.mp hb
  obtain ⟨k, hk⟩ := cert ⟨a, by omega⟩ ⟨b, by omega⟩ ha'.1 hb'.1
  exact ⟨k.val, hk⟩

private lemma next_cubic (b : ℕ) (hb : b ∈ Finset.Icc 1 10) :
    ((nextResidue b) ^ 3 + nextResidue b * b ^ 2 + b ^ 3) % 11 = 0 := by
  have cert : ∀ b : Fin 11,
      ((nextResidue b.val) ^ 3 + nextResidue b.val * b.val ^ 2 + b.val ^ 3) % 11 = 0 := by
    decide
  have h := Finset.mem_Icc.mp hb
  exact cert ⟨b, by omega⟩

theorem cross_partition (A B : Finset ℕ) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : A ∩ B = ∅) (hAUB : A ∪ B = Finset.Icc 1 10) :
    ∃ a ∈ A, ∃ b ∈ B, (a ^ 3 + a * b ^ 2 + b ^ 3) % 11 = 0 := by
  by_contra hcross
  have in_interval (x : ℕ) (hx : x ∈ A ∨ x ∈ B) : x ∈ Finset.Icc 1 10 := by
    rw [← hAUB]
    exact Finset.mem_union.mpr hx
  have hclosed (b : ℕ) (hb : b ∈ B) : nextResidue b ∈ B := by
    have hbI := in_interval b (Or.inr hb)
    have hn := next_mem b hbI
    rw [← hAUB, Finset.mem_union] at hn
    rcases hn with ha | hb'
    · exact False.elim (hcross ⟨nextResidue b, ha, b, hb, next_cubic b hbI⟩)
    · exact hb'
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  obtain ⟨k, hk⟩ := orbit_hits a b (in_interval a (Or.inl ha))
    (in_interval b (Or.inr hb))
  have hiter : ∀ j : ℕ, nextResidue^[j] b ∈ B := by
    intro j
    induction j with
    | zero => exact hb
    | succ j ih =>
      simpa only [Function.iterate_succ_apply'] using hclosed _ ih
  have hab : a ∈ A ∩ B := Finset.mem_inter.mpr ⟨ha, hk ▸ hiter k⟩
  rw [hAB] at hab
  simpa using hab

theorem solution (A B : Finset ℕ) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : A ∩ B = ∅) (hAUB : A ∪ B = Finset.Icc 1 10) :
    ∃ a b, (a ^ 3 + a * b ^ 2 + b ^ 3) % 11 = 0 := by
  obtain ⟨a, _, b, _, hab⟩ := cross_partition A B hA hB hAB hAUB
  exact ⟨a, b, hab⟩
