-- Prove2me | solution 1 for Singmaster.choose_cross
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:01:09.912849+00:00
-- url     : https://prove2.me/submissions/1caf705f-56b7-4fcb-b2e0-c3fdf9f02260

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
theorem solution{j m : ℕ} (hm : 2 ≤ m)
    (h : (j + m + 1) * (j + 2) = m * (m - 1)) :
    (j + m + 1).choose (j + 1) = (j + m).choose (j + 2) := by
  set N := j + m with hN
  set A := (N + 1).choose (j + 1) with hA
  set B := N.choose (j + 2) with hB
  set P := N.choose j with hP
  set Q := N.choose (j + 1) with hQ
  have e1 : (N + 1) * P = A * (j + 1) := Nat.add_one_mul_choose_eq N j
  have e2 : Q * (j + 1) = P * m := by
    rw [hQ, hP, Nat.choose_succ_right_eq]
    congr 1
    omega
  have e3 : B * (j + 2) = Q * (m - 1) := by
    rw [hB, hQ, show j + 2 = (j + 1) + 1 from rfl, Nat.choose_succ_right_eq]
    congr 1
    omega
  have key : A * ((j + 1) * (j + 2)) = B * ((j + 1) * (j + 2)) := by
    calc A * ((j + 1) * (j + 2)) = (A * (j + 1)) * (j + 2) := by ring
      _ = ((N + 1) * P) * (j + 2) := by rw [e1]
      _ = P * ((N + 1) * (j + 2)) := by ring
      _ = P * (m * (m - 1)) := by rw [h]
      _ = (P * m) * (m - 1) := by ring
      _ = (Q * (j + 1)) * (m - 1) := by rw [e2]
      _ = (Q * (m - 1)) * (j + 1) := by ring
      _ = (B * (j + 2)) * (j + 1) := by rw [e3]
      _ = B * ((j + 1) * (j + 2)) := by ring
  exact Nat.eq_of_mul_eq_mul_right (by positivity) key
