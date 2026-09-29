-- Prove2me | solution 1 for FermatPosition.degenerate_second_block_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T18:02:07.818962+00:00
-- url     : https://prove2.me/submissions/d51221b4-65c4-456b-8163-09f1b1c95075

import Mathlib
import Definitions.Def_NumberTheory_FermatPositionDensity
import Definitions.Def_NumberTheory_FermatPositionGeometry
import Definitions.Def_NumberTheory_FermatPositionNonlocality
open FermatPosition in
theorem solution (n : ℕ) : posCount degHit (2 ^ n) (2 ^ n) ≤ 1 := by
  unfold posCount
  -- every hit in the second block is the single position `2ⁿ - 1`
  have key : ∀ i ∈ (Finset.range (2 ^ n)).filter (fun i : ℕ => degHit ((2 : ℤ) ^ n + (i : ℤ))),
      i = 2 ^ n - 1 := by
    intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨hlt, hhit⟩ := hi
    unfold degHit sieveVal at hhit
    have h1 : ((1 : ℤ) + ((2 : ℤ) ^ n + (i : ℤ))) ^ 2 - 0 = (((2 ^ n + 1 + i) ^ 2 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [h1, Int.natAbs_natCast, Nat.mem_smoothNumbers'] at hhit
    -- a `3`-smooth square has only the prime `2`, so `2ⁿ + 1 + i` is a power of two
    have hpow : 2 ^ n + 1 + i = 2 ^ ((2 ^ n + 1 + i).primeFactorsList.length) := by
      apply Nat.eq_prime_pow_of_unique_prime_dvd (by omega)
      intro d hd hdvd
      have h3 := hhit d hd (dvd_pow hdvd two_ne_zero)
      have h2 := hd.two_le
      omega
    set e := (2 ^ n + 1 + i).primeFactorsList.length
    have hlo : 2 ^ n < 2 ^ e := by omega
    have hhi : 2 ^ e ≤ 2 ^ (n + 1) := by rw [pow_succ]; omega
    have he1 : n < e := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlo
    have he2 : e ≤ n + 1 := (Nat.pow_le_pow_iff_right (by norm_num)).mp hhi
    have he : e = n + 1 := by omega
    rw [he, pow_succ] at hpow
    omega
  exact Finset.card_le_one.mpr fun a ha b hb => (key a ha).trans (key b hb).symm
