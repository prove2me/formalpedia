-- Prove2me | solution 1 for znams_problem
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:17:58.491443+00:00
-- url     : https://prove2.me/submissions/3c7b6c20-10f6-4809-89e3-ea22222e48b4

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

open Finset

private theorem sylvester_sets (k : ℕ) :
    ∃ S : Finset ℕ, S.card = k ∧ (∀ x ∈ S, 1 < x) ∧
      ∀ x ∈ S, x ∣ 1 + ∏ y ∈ S.erase x, y := by
  induction k with
  | zero => exact ⟨∅, by simp⟩
  | succ k ih =>
    obtain ⟨S, hcard, hpos, hdiv⟩ := ih
    let P := ∏ x ∈ S, x
    have hP : 0 < P := Finset.prod_pos (fun x hx => lt_trans Nat.zero_lt_one (hpos x hx))
    have hbound (x : ℕ) (hx : x ∈ S) : x ≤ P :=
      Finset.single_le_prod' (fun y hy => (hpos y hy).le) hx
    have hnew : P + 1 ∉ S := by
      intro h
      have := hbound (P + 1) h
      omega
    refine ⟨insert (P + 1) S, by simp [hnew, hcard], ?_, ?_⟩
    · intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · omega
      · exact hpos x hx
    · intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · rw [erase_insert hnew]
        change P + 1 ∣ 1 + P
        rw [Nat.add_comm P 1]
      · have hne : P + 1 ≠ x := fun h => hnew (h.symm ▸ hx)
        have hxP : x ∣ P := Finset.dvd_prod_of_mem id hx
        have hmul : x ∣ P * ∏ y ∈ S.erase x, y := dvd_mul_of_dvd_left hxP _
        have hsum := dvd_add (hdiv x hx) hmul
        rw [erase_insert_of_ne hne, prod_insert]
        · convert hsum using 1 <;> ring
        · exact fun h => hnew (mem_of_mem_erase h)

private theorem distinct_sylvester_family (k : ℕ) :
    ∃ s : Fin k → ℕ, Function.Injective s ∧ (∀ i, 1 < s i) ∧
      ∀ i, s i ∣ 1 + ∏ j ∈ Finset.univ.erase i, s j := by
  classical
  obtain ⟨S, hcard, hpos, hdiv⟩ := sylvester_sets k
  let e : Fin k ≃ S := (S.equivFinOfCardEq hcard).symm
  let s : Fin k → ℕ := fun i => (e i).val
  have hinj : Function.Injective s := Subtype.val_injective.comp e.injective
  refine ⟨s, hinj, fun i => hpos _ (e i).property, ?_⟩
  intro i
  have hprod : (∏ j ∈ Finset.univ.erase i, s j) = ∏ y ∈ S.erase (s i), y := by
    apply Finset.prod_bij (fun j _ => s j)
    · intro j hj
      exact mem_erase.mpr ⟨fun heq => (mem_erase.mp hj).1 (hinj heq), (e j).property⟩
    · intro a _ b _ h
      exact hinj h
    · intro y hy
      obtain ⟨j, hj⟩ := e.surjective ⟨y, (mem_erase.mp hy).2⟩
      have hval : s j = y := congrArg Subtype.val hj
      refine ⟨j, mem_erase.mpr ⟨?_, mem_univ j⟩, hval⟩
      intro hji
      exact (mem_erase.mp hy).1 (hval.symm.trans (congrArg s hji))
    · intro j _
      rfl
  rw [hprod]
  exact hdiv _ (e i).property

theorem solution (k : ℕ) (hk : 2 ≤ k) :
    ∃ s : Fin k → ℕ,
      (∀ i, 0 < s i) ∧
      ∀ i, s i ∣ (1 + ∏ j ∈ Finset.univ.erase i, s j) := by
  obtain ⟨s, _, hpos, hdiv⟩ := distinct_sylvester_family k
  exact ⟨s, fun i => lt_trans Nat.zero_lt_one (hpos i), hdiv⟩
