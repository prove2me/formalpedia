-- Prove2me | Definitions.Def_Applications_Pythagorean_FibonacciEntryPoints
-- name    : Applications_Pythagorean_FibonacciEntryPoints
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:33.812237+00:00
-- url     : https://prove2.me/theorems/6e8c9c47-66f2-46da-982d-48ea78b707b5
-- title:
--   Aether Catalog definitions — Applications_Pythagorean_FibonacciEntryPoints
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.Pythagorean.FibonacciEntryPoints`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/Pythagorean/FibonacciEntryPoints.lean by skeleton subtraction
import Mathlib

/-! # Fibonacci entry points and primitive prime divisors

The *entry point* (or *rank of apparition*) of a prime `p` is the least positive
index `k` with `p ∣ F_k`.  This file develops the basic divisibility theory of
entry points entirely from `Nat.fib_gcd` and `Nat.fib_dvd`, and uses it to give a
clean characterization of *primitive prime divisors* of Fibonacci numbers (a prime
dividing `F_n` but none of `F_1, …, F_{n-1}`).

These results form the analytic backbone of Carmichael's primitive-divisor theorem
for Fibonacci numbers (cf. the catalog files `Speculative.AutoResearch.CarmichaelComposite`
and `Shared.CarmichaelProof`, where `fibEntryPt` and `fib_dvd_gcd_of_dvd` appear),
but here everything is proved self-containedly against Mathlib.

Main results:
* `fib_dvd_gcd`            — `p ∣ F_m → p ∣ F_n → p ∣ F_{gcd m n}`.
* `dvd_fib_iff_entry_dvd`  — `p ∣ F_n ↔ entryPoint p ∣ n` (for `p` ever dividing a Fibonacci).
* `primitive_iff_entry_eq` — `p` is a primitive prime divisor of `F_n` iff `entryPoint p = n`.
* `fib_twelve_no_primitive`— the classical exception: `F_12 = 144` has *no* primitive prime divisor.
-/

namespace FibonacciEntryPoints

open Classical in
/-- The Fibonacci entry point (rank of apparition) of `p`: the least `k > 0` with
`p ∣ F_k`, or `0` if no such `k` exists. -/
noncomputable def entryPoint (p : ℕ) : ℕ :=
  if h : ∃ k, 0 < k ∧ p ∣ Nat.fib k then Nat.find h else 0

/-
!-- The gcd–Fibonacci bridge: if `p` divides two Fibonacci numbers it divides the
one at their gcd, since `F_{gcd m n} = gcd (F_m) (F_n)` (`Nat.fib_gcd`). -- !--
-/

/-
!-- Existence/minimality package for the entry point, read off `Nat.find`. -- !--
-/



/-
!-- `p ∣ F_n ↔ entryPoint p ∣ n`.  (←) uses `entryPoint p ∣ n → F_{entryPoint p} ∣ F_n`
(`Nat.fib_dvd`); (→) uses the gcd bridge plus minimality. -- !--
-/

/-- `p` is a *primitive prime divisor* of `F_n`: it divides `F_n` but none of the
earlier Fibonacci numbers. -/
def IsPrimitive (p n : ℕ) : Prop :=
  p ∣ Nat.fib n ∧ ∀ k, 0 < k → k < n → ¬ p ∣ Nat.fib k

/-
!-- A prime that ever divides a Fibonacci is a primitive divisor of `F_n` exactly when
its entry point is `n`: minimality gives (←), and divisibility + minimality give (→). -- !--
-/

/-
!-- The classical exception `n = 12`: `F_12 = 144 = 2^4·3^2`, and `2 ∣ F_3`, `3 ∣ F_4`,
so every prime divisor of `F_12` already appears earlier — no primitive divisor exists. -- !--
-/

end FibonacciEntryPoints


