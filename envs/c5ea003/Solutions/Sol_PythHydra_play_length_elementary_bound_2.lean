-- Prove2me | solution 2 for PythHydra.play_length_elementary_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T18:49:54.006787+00:00
-- url     : https://prove2.me/submissions/48fc3b75-3471-4c5f-8551-0cd45901d83f

import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_HydraGame
open PythHydra Multiset in
theorem solution {k N L : ℕ} {H H' : Multiset ℕ}
    (hL : ∀ x ∈ H, x ≤ L) (h : StepsTo k N H H') :
    N ≤ Multiset.card H * (k + 1) ^ (L + 1) := by
  have hphi_zero : phi k 0 = 1 := by simp [phi]
  have hphi_succ : ∀ n : ℕ, phi k (n + 1) = 1 + k * phi k n := by
    intro n
    unfold phi
    rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero, add_comm]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hphi_mono : ∀ a b : ℕ, a ≤ b → phi k a ≤ phi k b := by
    intro a b hab
    unfold phi
    exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))
  have hphi_pos : ∀ n : ℕ, 1 ≤ phi k n := by
    intro n
    cases n with
    | zero => rw [hphi_zero]
    | succ n => rw [hphi_succ]; omega
  have hPhi_cons : ∀ (m : ℕ) (H : Multiset ℕ), Phi k (m ::ₘ H) = phi k m + Phi k H := by
    intro m H
    simp [Phi]
  have hPhi_add : ∀ A B : Multiset ℕ, Phi k (A + B) = Phi k A + Phi k B := by
    intro A B
    simp [Phi]
  have hPhi_nil : Phi k 0 = 0 := by simp [Phi]
  have hPhi_rep : ∀ c n : ℕ, Phi k (Multiset.replicate c n) = c * phi k n := by
    intro c n
    simp [Phi, Multiset.map_replicate, Multiset.sum_replicate]
  have hPhi_eq_zero : ∀ H : Multiset ℕ, Phi k H = 0 → H = 0 := by
    intro H hH
    induction H using Multiset.induction_on with
    | empty => rfl
    | cons m H _ =>
      rw [hPhi_cons] at hH
      have := hphi_pos m
      omega
  have hPhi_le : ∀ (H : Multiset ℕ) (L : ℕ), (∀ x ∈ H, x ≤ L) → Phi k H ≤ Multiset.card H * phi k L := by
    intro H L hL
    unfold Phi
    have := Multiset.sum_le_card_nsmul (H.map (phi k)) (phi k L) (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
      exact hphi_mono x L (hL x hx))
    simpa using this
  have hPhi_R : ∀ (m : ℕ) (R : Multiset ℕ), (∀ x ∈ R, x < m) → Multiset.card R ≤ k →
      Phi k R + 1 ≤ phi k m := by
    intro m R hlt hcard
    cases m with
    | zero =>
      have hR : R = 0 := Multiset.eq_zero_of_forall_notMem (fun x hx => by
        have := hlt x hx
        omega)
      subst hR
      rw [hPhi_nil, hphi_zero]
    | succ n =>
      have h1 := hPhi_le R n (fun x hx => by have := hlt x hx; omega)
      have h2 : Multiset.card R * phi k n ≤ k * phi k n := Nat.mul_le_mul_right _ hcard
      rw [hphi_succ]
      omega
  have hstep_dec : ∀ H H' : Multiset ℕ, HydraStep k H H' → Phi k H' + 1 ≤ Phi k H := by
    intro H H' hs
    cases hs with
    | chop m H R hlt hcard =>
      rw [hPhi_add, hPhi_cons]
      have := hPhi_R m R hlt hcard
      omega
  have hsteps : ∀ (n : ℕ) (H H' : Multiset ℕ), StepsTo k n H H' → n + Phi k H' ≤ Phi k H := by
    intro n
    induction n with
    | zero =>
      intro H H' h
      have e : H = H' := h
      subst e
      omega
    | succ n ih =>
      intro H H' h
      obtain ⟨M, hs, hr⟩ := h
      have := hstep_dec H M hs
      have := ih M H' hr
      omega
  have hphi_le : ∀ n : ℕ, phi k n ≤ (k + 1) ^ n := by
    intro n
    induction n with
    | zero => rw [hphi_zero, pow_zero]
    | succ n ih =>
      rw [hphi_succ, pow_succ]
      have := Nat.one_le_pow n (k + 1) (by omega)
      nlinarith
  have h1 := hsteps N H H' h
  have h2 := hPhi_le H L hL
  have h3 : phi k L ≤ (k + 1) ^ (L + 1) :=
    (hphi_le L).trans (Nat.pow_le_pow_right (by omega) (by omega))
  calc N ≤ Phi k H := by omega
    _ ≤ Multiset.card H * phi k L := h2
    _ ≤ Multiset.card H * (k + 1) ^ (L + 1) := Nat.mul_le_mul_left _ h3
