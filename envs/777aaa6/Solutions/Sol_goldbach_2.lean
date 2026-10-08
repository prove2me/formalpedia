-- Prove2me | solution 2 for goldbach
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T17:50:00.474228+00:00
-- url     : https://prove2.me/submissions/0259acb8-6180-412a-9841-cbed993709c6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_verified_two_odd_primes_to_4e18
import Theorems.Thm_Goldbach_vonMangoldt_convolution_extract_prime_pair
import Theorems.Thm_Goldbach_vonMangoldt_convolution_lower_bound_above_verified_range
import Mathlib.Tactic
set_option autoImplicit false

theorem solution : ∀ n : ℕ, 2 < n → Even n →
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p+q := by
  intro n hn he
  by_cases hlarge : 4*10^18 < n
  · exact Goldbach.vonMangoldt_convolution_extract_prime_pair n
      (Goldbach.vonMangoldt_convolution_lower_bound_above_verified_range n hlarge he)
  · by_cases h4 : n=4
    · subst n
      exact ⟨2,2,by norm_num,by norm_num,by norm_num⟩
    · have h6 : 6 ≤ n := by
        obtain ⟨k,hk⟩ := he
        omega
      obtain ⟨p,q,hp,hq,_hop,_hoq,hpq⟩ :=
        WeakGoldbach.verified_two_odd_primes_to_4e18 n h6 (by omega) he
      exact ⟨p,q,hp,hq,hpq⟩

#print axioms solution
