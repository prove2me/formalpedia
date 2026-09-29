-- Prove2me | solution 2 for PythHydra.exists_step_Phi_pred
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T18:45:28.742482+00:00
-- url     : https://prove2.me/submissions/31272d1f-269a-4f88-8914-b70700e2ea2c

import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_HydraGame
open PythHydra Multiset in
theorem solution {k : ℕ} {H : Multiset ℕ} (hH : H ≠ 0) :
    ∃ H', HydraStep k H H' ∧ Phi k H' + 1 = Phi k H := by
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
  have hexstep : ∀ H : Multiset ℕ, H ≠ 0 → ∃ H', HydraStep k H H' ∧ Phi k H' + 1 = Phi k H := by
    intro H hH
    obtain ⟨m, hm⟩ := Multiset.exists_mem_of_ne_zero hH
    obtain ⟨H₀, rfl⟩ := Multiset.exists_cons_of_mem hm
    cases m with
    | zero =>
      refine ⟨0 + H₀, HydraStep.chop 0 H₀ 0 (by simp) (by simp), ?_⟩
      rw [hPhi_add, hPhi_cons, hphi_zero, hPhi_nil]
      omega
    | succ n =>
      refine ⟨Multiset.replicate k n + H₀, HydraStep.chop (n + 1) H₀ _
        (fun x hx => by rw [Multiset.eq_of_mem_replicate hx]; omega) (by simp), ?_⟩
      rw [hPhi_add, hPhi_cons, hPhi_rep, hphi_succ]
      ring
  exact hexstep H hH
