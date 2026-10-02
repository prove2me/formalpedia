-- Prove2me | solution 1 for BookSixth.perm_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T09:16:39.595981+00:00
-- url     : https://prove2.me/submissions/832d9f99-1a78-43a3-b46e-f8298def1d48

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (n : Nat) (hn : 0 < n) (i c : Fin n) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ i = c)).card
      = (n - 1).factorial := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 :=
    Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
  let c₀ : Fin (k + 1) := ⟨0, Nat.zero_lt_succ k⟩
  -- all fibers have equal size, via left multiplication by a swap
  have hsym : ∀ d : Fin (k + 1),
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin (k + 1)) => σ i = d)).card
        = (Finset.univ.filter
          (fun σ : Equiv.Perm (Fin (k + 1)) => σ i = c₀)).card := by
    intro d
    let e : Equiv.Perm (Fin (k + 1)) ↪ Equiv.Perm (Fin (k + 1)) :=
      Equiv.mulLeft (Equiv.swap d c₀)
    have himg : (Finset.univ.filter
        (fun σ : Equiv.Perm (Fin (k + 1)) => σ i = d)).map e
        = Finset.univ.filter
          (fun σ : Equiv.Perm (Fin (k + 1)) => σ i = c₀) := by
      ext τ
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ,
        true_and]
      constructor
      · rintro ⟨σ, hσ, rfl⟩
        show (Equiv.swap d c₀ * σ) i = c₀
        rw [Equiv.Perm.mul_apply, hσ, Equiv.swap_apply_left]
      · intro hτ
        refine ⟨Equiv.swap d c₀ * τ, ?_, ?_⟩
        · show (Equiv.swap d c₀ * τ) i = d
          rw [Equiv.Perm.mul_apply, hτ, Equiv.swap_apply_right]
        · show Equiv.swap d c₀ * (Equiv.swap d c₀ * τ) = τ
          rw [← mul_assoc, Equiv.swap_mul_self, one_mul]
    rw [← himg, Finset.card_map]
  -- fibers partition the group
  have htot : ∑ d : Fin (k + 1),
      (Finset.univ.filter
        (fun σ : Equiv.Perm (Fin (k + 1)) => σ i = d)).card
      = (k + 1).factorial := by
    have h := Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset (Equiv.Perm (Fin (k + 1)))))
      (t := (Finset.univ : Finset (Fin (k + 1))))
      (f := fun σ => σ i) (fun x _ => Finset.mem_univ _)
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at h
    exact h.symm
  rw [Finset.sum_congr rfl (fun d _ => hsym d)] at htot
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at htot
  rw [Nat.factorial_succ] at htot
  have hcancel := Nat.mul_left_cancel (Nat.succ_pos k) htot
  rw [hsym c, Nat.add_sub_cancel]
  exact hcancel
