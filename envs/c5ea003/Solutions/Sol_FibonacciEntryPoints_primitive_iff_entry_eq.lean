-- Prove2me | solution 1 for FibonacciEntryPoints.primitive_iff_entry_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T12:24:17.911984+00:00
-- url     : https://prove2.me/submissions/a827afc8-0100-41a4-8237-0951ad7b3f50

-- Sol generated from Applications/Pythagorean/FibonacciEntryPoints.lean
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
theorem entryPoint_pos (p : ℕ) (hex : ∃ k, 0 < k ∧ p ∣ Nat.fib k) :
    0 < entryPoint p := by
  unfold entryPoint; aesop;

theorem dvd_fib_entryPoint (p : ℕ) (hex : ∃ k, 0 < k ∧ p ∣ Nat.fib k) :
    p ∣ Nat.fib (entryPoint p) := by
  convert Nat.find_spec hex |>.2 using 1;
  unfold entryPoint; aesop;

theorem entryPoint_min (p m : ℕ) (hm : 0 < m) (hlt : m < entryPoint p) :
    ¬ p ∣ Nat.fib m := by
  contrapose! hlt; unfold entryPoint at *; aesop;

/-
!-- `p ∣ F_n ↔ entryPoint p ∣ n`.  (←) uses `entryPoint p ∣ n → F_{entryPoint p} ∣ F_n`
(`Nat.fib_dvd`); (→) uses the gcd bridge plus minimality. -- !--
-/


/-
!-- A prime that ever divides a Fibonacci is a primitive divisor of `F_n` exactly when
its entry point is `n`: minimality gives (←), and divisibility + minimality give (→). -- !--
-/

/-
!-- The classical exception `n = 12`: `F_12 = 144 = 2^4·3^2`, and `2 ∣ F_3`, `3 ∣ F_4`,
so every prime divisor of `F_12` already appears earlier — no primitive divisor exists. -- !--
-/

/- Sanity check: `13 ∣ F_7 = 13` and `13` divides no earlier Fibonacci number, so by
`primitive_iff_entry_eq` the entry point of `13` is exactly `7`. -/
-- example : entryPoint 13 = 7 := by
--   have hex : ∃ k, 0 < k ∧ (13 : ℕ) ∣ Nat.fib k := ⟨7, by decide, by decide⟩
--   refine (primitive_iff_entry_eq 13 7 (by decide) hex).1 ?_
--   refine ⟨by decide, ?_⟩
--   intro k hk hk'
--   interval_cases k <;> decide -/


open FibonacciEntryPoints in
theorem solution(p n : ℕ) (hn : 0 < n)
    (hex : ∃ k, 0 < k ∧ p ∣ Nat.fib k) :
    IsPrimitive p n ↔ entryPoint p = n := by
  constructor <;> intro h;
  · apply le_antisymm;
    · obtain ⟨ k, hk₁, hk₂ ⟩ := hex;
      -- By definition of `entryPoint`, we know that `entryPoint p` is the smallest positive integer `k` such that `p ∣ Nat.fib k`.
      have h_entryPoint_def : entryPoint p = Nat.find (show ∃ k, 0 < k ∧ p ∣ Nat.fib k from ⟨k, hk₁, hk₂⟩) := by
                                                        exact dif_pos ⟨ k, hk₁, hk₂ ⟩;
      exact h_entryPoint_def.symm ▸ Nat.find_min' _ ⟨ hn, h.1 ⟩;
    · exact le_of_not_gt fun h' => h.2 _ ( entryPoint_pos _ hex ) h' ( dvd_fib_entryPoint _ hex );
  · refine' ⟨ _, fun k hk₁ hk₂ => _ ⟩;
    · exact h ▸ dvd_fib_entryPoint p hex;
    · exact entryPoint_min p k hk₁ ( by linarith )
