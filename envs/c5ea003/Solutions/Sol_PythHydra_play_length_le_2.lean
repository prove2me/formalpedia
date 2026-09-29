-- Prove2me | solution 2 for PythHydra.play_length_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T23:58:39.967681+00:00
-- url     : https://prove2.me/submissions/caf9b080-a366-498d-aec5-4e41d95841ad

import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_HydraGame
open PythHydra in
theorem solution {k N : ℕ} {H H' : Multiset ℕ} (h : StepsTo k N H H') : N ≤ Phi k H := by
  have hdrop : ∀ X Y : Multiset ℕ, HydraStep k X Y → Phi k Y + 1 ≤ Phi k X := by
    intro X Y hstep
    have hPhiadd : ∀ X Y : Multiset ℕ, Phi k (X + Y) = Phi k X + Phi k Y := by
      intro X Y; simp [Phi]
    have hPhicons : ∀ (a : ℕ) (X : Multiset ℕ), Phi k (a ::ₘ X) = phi k a + Phi k X := by
      intro a X; simp [Phi]
    have hphi_succ : ∀ t : ℕ, phi k (t + 1) = k * phi k t + 1 := by
      intro t
      unfold phi
      rw [Finset.sum_range_succ' (fun i => k ^ i) (t + 1)]
      simp [pow_succ, Finset.mul_sum, mul_comm]
    cases hstep with
    | chop m Hzz R hlt hcard =>
      rw [hPhiadd, hPhicons]
      have key : Phi k R + 1 ≤ phi k m := by
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · have hR : R = 0 := by
            by_contra hR
            obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hR
            exact absurd (hlt x hx) (Nat.not_lt_zero x)
          subst hR
          simp [Phi, phi]
        · obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
          have hmono : ∀ x ∈ R, phi k x ≤ phi k t := by
            intro x hx
            have hxt : x + 1 ≤ t + 1 := by have := hlt x hx; omega
            unfold phi
            exact Finset.sum_le_sum_of_subset (by simpa using hxt)
          have hle : Phi k R ≤ Multiset.card R * phi k t := by
            unfold Phi
            calc (R.map (phi k)).sum ≤ (R.map (fun _ => phi k t)).sum :=
                  Multiset.sum_map_le_sum_map _ _ hmono
              _ = Multiset.card R * phi k t := by
                  simp [Multiset.map_const', Multiset.sum_replicate, smul_eq_mul]
          have hle2 : Phi k R ≤ k * phi k t :=
            le_trans hle (Nat.mul_le_mul_right _ hcard)
          rw [hphi_succ t]
          omega
      omega
  induction N generalizing H with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    obtain ⟨M, hstep, hrest⟩ := h
    have h1 := ih hrest
    have h2 := hdrop H M hstep
    omega
