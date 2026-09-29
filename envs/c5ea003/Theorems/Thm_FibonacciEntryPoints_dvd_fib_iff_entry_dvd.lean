-- Prove2me | Theorems.Thm_FibonacciEntryPoints_dvd_fib_iff_entry_dvd
-- name    : FibonacciEntryPoints.dvd_fib_iff_entry_dvd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:52:27.041103+00:00
-- url     : https://prove2.me/theorems/fc34ef3a-ddd1-408b-9034-a1a0d7865afb
-- title:
--   Dvd fib iff entry dvd
-- statement:
--   Formal statement of `FibonacciEntryPoints.dvd_fib_iff_entry_dvd` from the Aether Catalog (Applications). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem FibonacciEntryPoints.dvd_fib_iff_entry_dvd(p n : ℕ) (hex : ∃ k, 0 < k ∧ p ∣ Nat.fib k) :
--       p ∣ Nat.fib n ↔ entryPoint p ∣ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/Pythagorean/FibonacciEntryPoints.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/Pythagorean/FibonacciEntryPoints.lean#L59

-- Thm stub generated from Applications/Pythagorean/FibonacciEntryPoints.lean
import Mathlib
import Definitions.Def_Applications_Pythagorean_FibonacciEntryPoints

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

open FibonacciEntryPoints


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

theorem FibonacciEntryPoints.dvd_fib_iff_entry_dvd(p n : ℕ) (hex : ∃ k, 0 < k ∧ p ∣ Nat.fib k) :
    p ∣ Nat.fib n ↔ entryPoint p ∣ n := by sorry
