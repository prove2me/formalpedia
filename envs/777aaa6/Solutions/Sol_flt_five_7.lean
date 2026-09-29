-- Prove2me | solution 7 for flt_five
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @tianyipeng
-- created : 2026-05-14T17:16:55.547578+00:00
-- url     : https://prove2.me/submissions/caffb5b7-79a8-485b-9350-70b22ed0f564
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring
import Theorems.Thm_flt_odd_prime_coprime_reduction
import Theorems.Thm_flt5_case1
import Theorems.Thm_flt5_descent_case2

-- Sketch: flt_five via Dirichlet descent
-- coprime_reduction → case split on 5|a'/b'/c' → descent_case2 or case1

theorem solution (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a ^ 5 + b ^ 5 ≠ c ^ 5 :=
  flt_odd_prime_coprime_reduction 5 (by decide) (by omega) a b c ha hb hc
    (fun a' b' c' ha' hb' hc' hab' hbc' hac' heq' => by
      have h_int : (↑a' : ℤ) ^ 5 + ↑b' ^ 5 = ↑c' ^ 5 := by exact_mod_cast heq'
      have h_igcd_ab : Int.gcd (↑a' : ℤ) ↑b' = 1 := by
        show Nat.gcd a' b' = 1; exact hab'
      by_cases h5c : (5 : ℤ) ∣ ↑c'
      · exact flt5_descent_case2 ↑a' ↑b' ↑c' h_int h_igcd_ab h5c
            (by exact_mod_cast hc'.ne')
      · by_cases h5a : (5 : ℤ) ∣ ↑a'
        · have h_int' : (↑c' : ℤ) ^ 5 + (-↑b') ^ 5 = ↑a' ^ 5 := by
            have neg5 : (-↑b' : ℤ) ^ 5 = -(↑b' : ℤ) ^ 5 := by ring
            rw [neg5]; omega
          have h_igcd_cb : Int.gcd (↑c' : ℤ) (-↑b') = 1 := by
            unfold Int.gcd; rw [Int.natAbs_neg]
            show Nat.gcd c' b' = 1
            rw [Nat.gcd_comm]; exact hbc'
          exact flt5_descent_case2 ↑c' (-↑b') ↑a' h_int' h_igcd_cb h5a
              (by exact_mod_cast ha'.ne')
        · by_cases h5b : (5 : ℤ) ∣ ↑b'
          · have h_int'' : (↑c' : ℤ) ^ 5 + (-↑a') ^ 5 = ↑b' ^ 5 := by
              have neg5 : (-↑a' : ℤ) ^ 5 = -(↑a' : ℤ) ^ 5 := by ring
              rw [neg5]; omega
            have h_igcd_ca : Int.gcd (↑c' : ℤ) (-↑a') = 1 := by
              unfold Int.gcd; rw [Int.natAbs_neg]
              show Nat.gcd c' a' = 1
              rw [Nat.gcd_comm]; exact hac'
            exact flt5_descent_case2 ↑c' (-↑a') ↑b' h_int'' h_igcd_ca h5b
                (by exact_mod_cast hb'.ne')
          · exact flt5_case1 ↑a' ↑b' ↑c' h_int h5a h5b h5c)
