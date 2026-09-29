-- Prove2me | solution 1 for fib_dvd_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:26:21.027914+00:00
-- url     : https://prove2.me/submissions/6b47534d-b08f-423d-825c-290021958a5f

-- Sol generated from Speculative/NumberTheory/FibonacciDivisibilityPigeonhole.lean
import Mathlib
import Definitions.Def_Speculative_NumberTheory_FibonacciDivisibilityPigeonhole
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Fib.Basic

/-!
# Fibonacci-Divisibility Pigeonhole Bridge

This file contains three theorems:

* `fib_dvd_of_dvd`: divisibility of indices implies divisibility of Fibonacci numbers.
* `fib_dvd_iff`: for `3 ≤ m`, `Nat.fib m ∣ Nat.fib n ↔ m ∣ n`.
* `divisibility_pigeonhole`: any `n+1` distinct numbers in `[1, 2n]` contain a
  divisibility pair.
-/

/-- If `m ∣ n` then `Nat.fib m ∣ Nat.fib n`. -/
theorem fib_dvd_of_dvd {m n : ℕ} (h : m ∣ n) : Nat.fib m ∣ Nat.fib n :=
  Nat.fib_dvd m n h




theorem solution{m n : ℕ} (hm : 3 ≤ m) : Nat.fib m ∣ Nat.fib n ↔ m ∣ n := by
  have hgcd : Nat.gcd (Nat.fib m) (Nat.fib n) = Nat.fib (Nat.gcd m n) :=
    (Nat.fib_gcd m n).symm
  by_cases h : m ∣ n <;> simp_all +decide [ Nat.dvd_iff_mod_eq_zero ];
  · exact Nat.mod_eq_zero_of_dvd <| fib_dvd_of_dvd <| Nat.dvd_of_mod_eq_zero h;
  · -- Since $n \not\equiv 0 \pmod{m}$, we have $\gcd(m, n) < m$.
    have h_gcd_lt_m : Nat.gcd m n < m := by
      exact lt_of_le_of_ne ( Nat.le_of_dvd ( by linarith ) ( Nat.gcd_dvd_left _ _ ) ) fun con => h <| Nat.mod_eq_zero_of_dvd <| con ▸ Nat.gcd_dvd_right _ _;
    -- Since $n \not\equiv 0 \pmod{m}$, we have $\gcd(m, n) < m$, and thus $F_{\gcd(m, n)} < F_m$.
    have h_fib_gcd_lt_fib_m : Nat.fib (Nat.gcd m n) < Nat.fib m := by
      by_cases h_gcd_ge_2 : 2 ≤ Nat.gcd m n;
      · rw [ Nat.fib_lt_fib ] <;> linarith;
      · interval_cases _ : Nat.gcd m n <;> simp_all +decide;
        exact Nat.le_trans ( by decide ) ( Nat.fib_mono hm );
    exact fun h' => h_fib_gcd_lt_fib_m.ne <| by have := Nat.gcd_eq_left ( Nat.dvd_of_mod_eq_zero h' ) ; linarith;
