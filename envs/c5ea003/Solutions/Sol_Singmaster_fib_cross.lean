-- Prove2me | solution 1 for Singmaster.fib_cross
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:05:16.485987+00:00
-- url     : https://prove2.me/submissions/0b689d66-2abd-4daa-b507-72bec00ed10b

-- Sol generated from Combinatorics/SingmasterFibonacci.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterFibonacci
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Theorems.Thm_Singmaster_cassini_odd
/-
# The Fibonacci family behind the "six times" phenomenon

Building on `Combinatorics.SingmasterOccurrences`, this file explains *why* infinitely
many numbers occur at least six times in Pascal's triangle.

The mechanism is a bridge between three different pieces of mathematics:

* **Combinatorics.**  A value `C(n,k)` normally occupies four positions —
  `(n,k)`, `(n,n-k)`, `(t,1)`, `(t,t-1)` where `t = C(n,k)`.  Two *extra* positions
  appear exactly when the same number also occurs one row higher, i.e. when
  `C(n,k) = C(n-1,k+1)`.
* **Arithmetic.**  Clearing factorials turns that coincidence into the Diophantine
  equation `n (k+1) = (n-k)(n-k-1)` (`Singmaster.choose_cross`).
* **The Fibonacci recursion.**  That equation is a disguised Pell equation, and
  Cassini's identity `F_{2i+3}^2 = F_{2i+2} F_{2i+4} + 1` produces an infinite family
  of solutions `n = F_{2i+4} F_{2i+5}`, `k = F_{2i+2} F_{2i+5}`.

For `i = 0` this is `n = 15`, `k = 5`, giving `C(15,5) = C(14,6) = 3003`; the next
member is `n = 104`, `k = 39`, giving `C(104,39) = C(103,40)`.

Main results:
* `Singmaster.choose_cross` — the cross-row identity from the Diophantine condition;
* `Singmaster.cassini_odd` — Cassini's identity at odd index, over `ℕ`;
* `Singmaster.fib_cross` — the Fibonacci solutions of the Diophantine condition;
* `Singmaster.six_le_mult_fib` — every member of the family occurs at least six times;
* `Singmaster.infinitely_many_six` — hence there are arbitrarily large such numbers.
-/

open Finset

open Singmaster

/-! ## The cross-row identity -/


/-! ## Cassini's identity at odd index -/


/-! ## The Fibonacci solutions -/


variable (i : ℕ)




theorem fib_two_add_two_pos (i : ℕ) : 1 ≤ Nat.fib (2 * i + 2) := by
  have h := Nat.fib_mono (show (2 : ℕ) ≤ 2 * i + 2 by omega)
  simpa using h

theorem fib_lt_fib_succ_of (i : ℕ) : Nat.fib (2 * i + 2) < Nat.fib (2 * i + 3) := by
  have h : Nat.fib (2 * i + 3) = Nat.fib (2 * i + 1) + Nat.fib (2 * i + 2) :=
    Nat.fib_add_two (n := 2 * i + 1)
  have h1 : 1 ≤ Nat.fib (2 * i + 1) := by
    have h2 := Nat.fib_mono (show (1 : ℕ) ≤ 2 * i + 1 by omega)
    simpa using h2
  omega

theorem five_le_fib (i : ℕ) : 5 ≤ Nat.fib (2 * i + 5) := by
  have h := Nat.fib_mono (show (5 : ℕ) ≤ 2 * i + 5 by omega)
  simpa using h




/-! ## Six occurrences -/




open Singmaster in
theorem solution(i : ℕ) :
    famRow i * (famCol i + 1) = (famRow i - famCol i) * (famRow i - famCol i - 1) := by
  set a := Nat.fib (2 * i + 2) with ha
  set b := Nat.fib (2 * i + 3) with hb
  set c := Nat.fib (2 * i + 4) with hc
  set d := Nat.fib (2 * i + 5) with hd
  have hcab : c = a + b := Nat.fib_add_two (n := 2 * i + 2)
  have hdbc : d = b + c := Nat.fib_add_two (n := 2 * i + 3)
  have hcas : b * b = a * c + 1 := cassini_odd i
  have ha1 : 1 ≤ a := fib_two_add_two_pos i
  have hd5 : 5 ≤ d := five_le_fib i
  have hrow : famRow i = c * d := rfl
  have hcol : famCol i = a * d := rfl
  have hsub : famRow i - famCol i = b * d := by
    show c * d - a * d = b * d
    rw [hcab, Nat.add_mul]
    omega
  have hbd : 5 ≤ b * d := by
    have hb2 : 2 ≤ b := by
      have := fib_lt_fib_succ_of i
      omega
    nlinarith
  rw [hsub, hrow, hcol]
  have hstep : c * d * (a * d + 1) + b * d = (b * d) * (b * d) := by
    have expand : (b * d) * (b * d) = (a * c + 1) * (d * d) := by
      rw [← hcas]; ring
    rw [expand, hdbc, hcab]
    ring
  have hmul : (b * d) * (b * d - 1) = (b * d) * (b * d) - b * d := by
    rw [Nat.mul_sub, Nat.mul_one]
  omega
