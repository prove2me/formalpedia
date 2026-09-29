-- Prove2me | solution 1 for fib_primitive_divisor_prime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T02:16:52.263156+00:00
-- url     : https://prove2.me/submissions/2b222c21-5825-4189-9e32-f2da2b9c6f86

-- Sol generated from Shared/CarmichaelHelper.lean
import Mathlib

/-! # Carmichael's theorem: the prime case

We prove that for a **prime** `n ≥ 13`, the Fibonacci number `F(n)` has a
*primitive* prime divisor: a prime `p` dividing `F(n)` but dividing no earlier
`F(k)` with `0 < k < n`.

The prime case is elementary.  Because `n` is prime, the only proper positive
divisor of `n` is `1`.  If a prime `p` divides both `F(n)` and `F(k)` for some
`0 < k < n`, then (using the strong divisibility property
`Nat.fib_gcd`) `p` divides `F(gcd n k)`.  But `gcd n k` divides the prime `n`
and is `< n`, so it equals `1`, forcing `p ∣ F(1) = 1`, a contradiction.  Since
`F(n) > 1` it has a prime divisor, and every such divisor is primitive.

This is the "prime half" that complements the computational/structural composite
case in `Shared.CarmichaelProof`.

-- !-- Lab Notes -- !--
* **Hypothesis (Hypothesizer).**  For prime `n`, *every* prime divisor of `F(n)`
  should already be primitive, since there are no nontrivial proper divisors of
  `n` to host an earlier occurrence.
* **Experiment (Experimenter).**  Formalized the `gcd`-collapse argument through
  `Nat.fib_gcd` and `Nat.Coprime`.  The single delicate point is `F(n) > 1`,
  handled by `Nat.fib` monotonicity from `n ≥ 13 ≥ 3`.
* **Analysis (Analyst).**  "True and clean": the primitivity is automatic; the
  only existence input is a prime factor of `F(n)`, from `Nat.exists_prime_and_dvd`.
* **Critique (Critic).**  Corner case `k = n` is excluded by `k < n`; `k = 0` is
  excluded by `0 < k`.  No hidden use of the composite machinery.
* **Synthesis (PI).**  Prime `n` is the base of Carmichael's theorem; the
  composite case reduces to controlling shared factors across proper divisors.
-/


theorem solution(n : ℕ) (hn : 13 ≤ n) (hnp : Nat.Prime n) :
    ∃ p, Nat.Prime p ∧ p ∣ Nat.fib n ∧
      ∀ k, 0 < k → k < n → ¬(p ∣ Nat.fib k) := by
  have hfib_gt : 1 < Nat.fib n := by
    have : Nat.fib 3 ≤ Nat.fib n := Nat.fib_mono (by omega)
    simpa [Nat.fib] using lt_of_lt_of_le (by decide : (1 : ℕ) < Nat.fib 3) this
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hfib_gt.ne'
  refine ⟨p, hp, hpn, ?_⟩
  intro k hk hkn hpk
  -- `p` divides `F(gcd n k)`
  have hgcd_dvd : p ∣ Nat.fib (Nat.gcd n k) := by
    rw [Nat.fib_gcd]; exact Nat.dvd_gcd hpn hpk
  -- `gcd n k` divides the prime `n` and is `< n`, hence equals `1`
  have hgcd_one : Nat.gcd n k = 1 := by
    rcases (Nat.Prime.eq_one_or_self_of_dvd hnp _ (Nat.gcd_dvd_left n k)) with h | h
    · exact h
    · have hle : Nat.gcd n k ≤ k := Nat.le_of_dvd hk (Nat.gcd_dvd_right n k)
      omega
  rw [hgcd_one, Nat.fib_one] at hgcd_dvd
  exact hp.not_dvd_one hgcd_dvd
