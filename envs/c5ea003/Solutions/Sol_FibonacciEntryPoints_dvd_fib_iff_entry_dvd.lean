-- Prove2me | solution 1 for FibonacciEntryPoints.dvd_fib_iff_entry_dvd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T12:24:17.388083+00:00
-- url     : https://prove2.me/submissions/2bd675cc-ae70-4347-917b-55b394b9d12f

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
theorem fib_dvd_gcd (p m n : ℕ) (hm : p ∣ Nat.fib m) (hn : p ∣ Nat.fib n) :
    p ∣ Nat.fib (Nat.gcd m n) := by
  convert Nat.dvd_gcd hm hn using 1;
  grind +suggestions

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
`primitive_iff_entry_eq` the entry point of `13` is exactly `7`.
example : entryPoint 13 = 7 := by
  have hex : ∃ k, 0 < k ∧ (13 : ℕ) ∣ Nat.fib k := ⟨7, by decide, by decide⟩
  refine (primitive_iff_entry_eq 13 7 (by decide) hex).1 ?_
  refine ⟨by decide, ?_⟩
  intro k hk hk'
  interval_cases k <;> decide -/


open FibonacciEntryPoints in
theorem solution(p n : ℕ) (hex : ∃ k, 0 < k ∧ p ∣ Nat.fib k) :
    p ∣ Nat.fib n ↔ entryPoint p ∣ n := by
  constructor;
  · -- Let e = entryPoint p, which is positive by entryPoint_pos hex, and p ∣ Nat.fib e by dvd_fib_entryPoint hex.
    set e := entryPoint p
    have he_pos : 0 < e := entryPoint_pos p hex
    have he_div : p ∣ Nat.fib e := dvd_fib_entryPoint p hex;
    intro hn;
    contrapose! hn;
    -- Since $e$ does not divide $n$, we have $\gcd(e, n) < e$.
    have h_gcd_lt_e : Nat.gcd e n < e := by
      exact lt_of_le_of_ne ( Nat.le_of_dvd he_pos ( Nat.gcd_dvd_left _ _ ) ) fun h => hn <| h.symm ▸ Nat.gcd_dvd_right _ _;
    exact fun h => entryPoint_min p ( Nat.gcd e n ) ( Nat.gcd_pos_of_pos_left _ he_pos ) h_gcd_lt_e <| fib_dvd_gcd p e n he_div h;
  · exact fun h => dvd_trans ( dvd_fib_entryPoint p hex ) ( Nat.fib_dvd _ _ h )
