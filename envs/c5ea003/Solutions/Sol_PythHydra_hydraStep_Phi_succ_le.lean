-- Prove2me | solution 1 for PythHydra.hydraStep_Phi_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T00:03:19.523685+00:00
-- url     : https://prove2.me/submissions/d63bedf3-5421-4b0e-a11d-0e947ea4a9a3

import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_HydraGame
open PythHydra in
theorem solution {k : ℕ} {H H' : Multiset ℕ} (h : HydraStep k H H') : Phi k H' + 1 ≤ Phi k H := by
  have hPhiadd : ∀ X Y : Multiset ℕ, Phi k (X + Y) = Phi k X + Phi k Y := by
    intro X Y; simp [Phi]
  have hPhicons : ∀ (a : ℕ) (X : Multiset ℕ), Phi k (a ::ₘ X) = phi k a + Phi k X := by
    intro a X; simp [Phi]
  have hphi_succ : ∀ t : ℕ, phi k (t + 1) = k * phi k t + 1 := by
    intro t
    unfold phi
    rw [Finset.sum_range_succ' (fun i => k ^ i) (t + 1)]
    simp [pow_succ, Finset.mul_sum, mul_comm]
  cases h with
  | chop m H0 R hlt hcard =>
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
