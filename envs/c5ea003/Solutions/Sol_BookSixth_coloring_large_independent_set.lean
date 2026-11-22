-- Prove2me | solution 1 for BookSixth.coloring_large_independent_set
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-16T14:15:50.876898+00:00
-- url     : https://prove2.me/submissions/eebbeda6-2079-4d79-8fcc-471689f01c6d

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators

set_option autoImplicit false

theorem solution (N k : Nat)
    (G : SimpleGraph (Fin N)) (c : Fin N -> Fin k)
    (hproper : forall u v, G.Adj u v -> c u != c v) :
    exists S : Finset (Fin N),
      Set.Pairwise (S : Set (Fin N)) (fun u v => Not (G.Adj u v)) /\
      Nat.le N (k * S.card) := by
  cases k with
  | zero =>
    have hN0 : N = 0 := by
      by_contra hN
      have hNpos : 0 < N := Nat.pos_of_ne_zero hN
      obtain ⟨x⟩ : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
      exact Fin.elim0 (c x)
    refine ⟨∅, ?_, ?_⟩
    · intro u hu v hv huv hadj
      simp at hu
    · rw [hN0, zero_mul]
      exact le_refl 0
  | succ k =>
    suffices hex : exists j : Fin (k + 1),
        Nat.le N ((k + 1) * ((Finset.univ.filter (fun a : Fin N => c a = j)).card)) by
      obtain ⟨j, hj⟩ := hex
      refine ⟨Finset.univ.filter (fun a : Fin N => c a = j), ?_, hj⟩
      intro u hu v hv huv hadj
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
      exact absurd (hu.trans hv.symm)
        ((bne_iff_ne (a := c u) (b := c v)).mp (hproper u v hadj))
    by_contra hcon
    push_neg at hcon
    have hpart : N = ∑ j : Fin (k + 1),
        ((Finset.univ.filter (fun a : Fin N => c a = j)).card) := by
      have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ)
        (f := c) (fun x _ => by simp)
      rwa [Finset.card_univ, Fintype.card_fin] at h
    have hlt : forall j : Fin (k + 1),
        ((k + 1) * ((Finset.univ.filter (fun a : Fin N => c a = j)).card)) < N :=
      fun j => not_le.mp (hcon j)
    have hsplit : ∑ j : Fin (k + 1),
        ((k + 1) * ((Finset.univ.filter (fun a : Fin N => c a = j)).card))
        = ((k + 1) * ((Finset.univ.filter (fun a : Fin N => c a = ⟨0, Nat.zero_lt_succ k⟩)).card))
        + Finset.sum (Finset.univ.erase (⟨0, Nat.zero_lt_succ k⟩ : Fin (k + 1)))
          (fun j => ((k + 1) * ((Finset.univ.filter (fun a : Fin N => c a = j)).card))) :=
      (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (⟨0, Nat.zero_lt_succ k⟩ : Fin (k + 1)))).symm
    have hle : Finset.sum (Finset.univ.erase (⟨0, Nat.zero_lt_succ k⟩ : Fin (k + 1)))
        (fun j => ((k + 1) * ((Finset.univ.filter (fun a : Fin N => c a = j)).card)))
        ≤ Finset.sum (Finset.univ.erase (⟨0, Nat.zero_lt_succ k⟩ : Fin (k + 1))) (fun _ => N) :=
      Finset.sum_le_sum (fun j _ => le_of_lt (hlt j))
    have hN : N + Finset.sum (Finset.univ.erase (⟨0, Nat.zero_lt_succ k⟩ : Fin (k + 1))) (fun _ => N)
        = ∑ _j : Fin (k + 1), N :=
      (Finset.add_sum_erase Finset.univ (fun _ => N)
        (Finset.mem_univ (⟨0, Nat.zero_lt_succ k⟩ : Fin (k + 1))))
    have hstrict : ∑ j : Fin (k + 1),
        ((k + 1) * ((Finset.univ.filter (fun a : Fin N => c a = j)).card))
        < ∑ _j : Fin (k + 1), N := by
      rw [hsplit, ← hN]
      exact add_lt_add_of_lt_of_le (hlt _) hle
    have hEq : ∑ j : Fin (k + 1),
        ((k + 1) * ((Finset.univ.filter (fun a : Fin N => c a = j)).card))
        = (k + 1) * N := by
      simp only [← Finset.mul_sum, ← hpart]
    have hNeq : ∑ _j : Fin (k + 1), N = (k + 1) * N := by
      rw [Finset.sum_const_nat (m := N) (fun _ _ => rfl), Finset.card_univ, Fintype.card_fin]
    omega
