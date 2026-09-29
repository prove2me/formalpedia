-- Prove2me | solution 1 for FactoringLab.factor_recovery_from_totient_nat
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:38:40.133922+00:00
-- url     : https://prove2.me/submissions/9e9376fa-b1bd-4a14-b730-c8fbdcf68aa5

-- Sol generated from Probability/MultiplicativeDichotomy.lean
import Mathlib
import Definitions.Def_Probability_SymmetryCircularity
import Theorems.Thm_FactoringLab_recovery_from_sum
import Theorems.Thm_FactoringLab_totient_semiprime
/-
# The multiplicative dichotomy

A sharpening of the structural-orthogonality thesis for the classical
multiplicative invariants of a semiprime `N = p*q` (`p ≠ q` prime).  Each such
invariant falls on exactly one of two sides:

* **Constant side (no information).**  The number of divisors, the number of
  distinct prime factors and the Möbius value are *literally constant* on the
  set of semiprimes: `4`, `2`, `1`.  They cannot distinguish any two
  semiprimes, let alone their factors
  (`FactoringLab.constant_invariants_carry_no_information`).
* **Circular side (as hard as factoring).**  The sum of divisors `σ₁` and
  Euler's totient `φ` both reveal `p + q` from `N`, and `(N, p+q)` recovers the
  factorization in closed form
  (`FactoringLab.factor_recovery_from_sigma`).  An invariant on this side does
  not help: computing it is already a factoring algorithm.

There is no third option among these classical invariants — which is exactly
the empirical "N-only or circular" pattern of the lab experiments.
-/

open FactoringLab

open ArithmeticFunction

/-! ### The constant side -/





/-! ### The circular side -/






/-! ### The dichotomy for the whole affine family -/



open FactoringLab in
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (hpq : p ≤ q) :
    let N : ℤ := (p * q : ℕ)
    let s : ℤ := N + 1 - (Nat.totient (p * q) : ℤ)
    ((s - (Int.sqrt (s ^ 2 - 4 * N) : ℤ)) / 2 = (p : ℤ)) ∧
      ((s + (Int.sqrt (s ^ 2 - 4 * N) : ℤ)) / 2 = (q : ℤ)) := by
  intro N s
  have htot : Nat.totient (p * q) = (p - 1) * (q - 1) := totient_semiprime hp hq hne
  have hp1 : 1 ≤ p := hp.one_lt.le.trans' (by norm_num)
  have hq1 : 1 ≤ q := hq.one_lt.le.trans' (by norm_num)
  have hcast : ((Nat.totient (p * q) : ℕ) : ℤ) = ((p : ℤ) - 1) * ((q : ℤ) - 1) := by
    rw [htot]
    push_cast [Nat.cast_sub hp1, Nat.cast_sub hq1]
    ring
  have hs : s = (p : ℤ) + q := by
    simp only [s, N, hcast]
    push_cast
    ring
  have hN : N = (p : ℤ) * q := by simp [N]
  obtain ⟨_, h1, h2⟩ :=
    recovery_from_sum (p := (p : ℤ)) (q := (q : ℤ)) (by exact_mod_cast hpq) hN hs
  exact ⟨h1, h2⟩
