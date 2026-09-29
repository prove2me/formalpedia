-- Prove2me | solution 1 for SocialChoice.incoherenceIndex_singleton_one
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T19:40:43.285513+00:00
-- url     : https://prove2.me/submissions/341966c0-ddfb-4103-8f18-6201e98508e7

import Mathlib
import Definitions.Def_Applications_SocialChoice_NonFiniteAxiomatization
open SocialChoice in
theorem solution {n : ℕ} (hn : 0 < n) : incoherenceIndex ({1} : Frame n) = n := by
  unfold incoherenceIndex
  -- `n` copies of the atom `1` balance
  have hmem : n ∈ balancedLengths ({1} : Frame n) := by
    refine ⟨List.replicate n 1, ⟨?_, ?_, ?_⟩, List.length_replicate⟩
    · simp only [ne_eq, List.replicate_eq_nil_iff]
      omega
    · intro x hx
      rw [List.eq_of_mem_replicate hx]
      simp
    · rw [List.sum_replicate, nsmul_eq_mul, mul_one, ZMod.natCast_self]
  apply le_antisymm (Nat.sInf_le hmem)
  apply le_csInf ⟨n, hmem⟩
  -- any balanced sequence is `k` copies of `1` with `n ∣ k`, `k ≥ 1`
  rintro k ⟨l, ⟨hne, hall, hsum⟩, rfl⟩
  have hl : l = List.replicate l.length 1 :=
    List.eq_replicate_iff.mpr ⟨rfl, fun x hx => by simpa using hall x hx⟩
  rw [hl, List.sum_replicate, nsmul_eq_mul, mul_one] at hsum
  have hdvd := (ZMod.natCast_eq_zero_iff _ _).mp hsum
  exact Nat.le_of_dvd (List.length_pos_of_ne_nil hne) hdvd
