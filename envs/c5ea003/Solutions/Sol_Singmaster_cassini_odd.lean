-- Prove2me | solution 1 for Singmaster.cassini_odd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:42:27.46564+00:00
-- url     : https://prove2.me/submissions/01b6dd00-ff22-48db-a4b2-a361be04fe57

-- Sol generated from Combinatorics/SingmasterFibonacci.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterFibonacci
import Definitions.Def_Combinatorics_SingmasterOccurrences
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










/-! ## Six occurrences -/




open Singmaster in
theorem solution(i : ℕ) :
    Nat.fib (2 * i + 3) * Nat.fib (2 * i + 3) = Nat.fib (2 * i + 2) * Nat.fib (2 * i + 4) + 1 := by
  induction i with
  | zero => decide
  | succ p ih =>
    have h1 : Nat.fib (2 * p + 4) = Nat.fib (2 * p + 2) + Nat.fib (2 * p + 3) :=
      Nat.fib_add_two (n := 2 * p + 2)
    have h2 : Nat.fib (2 * p + 5) = Nat.fib (2 * p + 3) + Nat.fib (2 * p + 4) :=
      Nat.fib_add_two (n := 2 * p + 3)
    have h3 : Nat.fib (2 * p + 6) = Nat.fib (2 * p + 4) + Nat.fib (2 * p + 5) :=
      Nat.fib_add_two (n := 2 * p + 4)
    have e1 : 2 * (p + 1) + 3 = 2 * p + 5 := by ring
    have e2 : 2 * (p + 1) + 2 = 2 * p + 4 := by ring
    have e3 : 2 * (p + 1) + 4 = 2 * p + 6 := by ring
    rw [e1, e2, e3, h3, h2, h1]
    rw [h1] at ih
    nlinarith [ih]
