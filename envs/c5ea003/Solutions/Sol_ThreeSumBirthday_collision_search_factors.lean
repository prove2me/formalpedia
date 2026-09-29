-- Prove2me | solution 1 for ThreeSumBirthday.collision_search_factors
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T00:53:22.758722+00:00
-- url     : https://prove2.me/submissions/663c72fc-c357-4ae2-b6ad-a1aed8459ddd

import Mathlib
import Definitions.Def_Speculative_AutoResearch_ThreeSumBirthdayHierarchy
open Finset in
theorem solution {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (S : Finset ℕ) (r : ℕ) (h : p < S.card.choose r) :
    ∃ A ∈ S.powersetCard r, ∃ B ∈ S.powersetCard r, A ≠ B ∧
      p ∣ (max (A.sum id) (B.sum id) - min (A.sum id) (B.sum id)) ∧
      (¬ q ∣ (max (A.sum id) (B.sum id) - min (A.sum id) (B.sum id)) →
        Nat.gcd (max (A.sum id) (B.sum id) - min (A.sum id) (B.sum id)) (p * q) = p) := by
  -- pigeonhole: more `r`-subsets than residues mod `p`
  have hc : (range p).card < (S.powersetCard r).card := by
    rw [card_range, card_powersetCard]
    exact h
  obtain ⟨A, hA, B, hB, hAB, hmod⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hc
    (f := fun A : Finset ℕ => A.sum id % p) (fun A _ => mem_range.2 (Nat.mod_lt _ hp.pos))
  refine ⟨A, hA, B, hB, hAB, ?_, ?_⟩
  · -- equal residues: `p` divides the difference of the sums
    rcases le_total (A.sum id) (B.sum id) with hle | hle
    · rw [max_eq_right hle, min_eq_left hle]
      exact (Nat.modEq_iff_dvd' hle).1 hmod
    · rw [max_eq_left hle, min_eq_right hle]
      exact (Nat.modEq_iff_dvd' hle).1 hmod.symm
  · -- if `q` does not divide it, the `q`-part of the gcd is trivial
    intro hnq
    have hpd : p ∣ (max (A.sum id) (B.sum id) - min (A.sum id) (B.sum id)) := by
      rcases le_total (A.sum id) (B.sum id) with hle | hle
      · rw [max_eq_right hle, min_eq_left hle]
        exact (Nat.modEq_iff_dvd' hle).1 hmod
      · rw [max_eq_left hle, min_eq_right hle]
        exact (Nat.modEq_iff_dvd' hle).1 hmod.symm
    obtain ⟨d, hd⟩ := hpd
    rw [hd] at hnq ⊢
    have hqd : ¬ q ∣ d := fun h => hnq (Dvd.dvd.mul_left h p)
    have hcop : Nat.Coprime d q := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hq).2 hqd))
    rw [Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
