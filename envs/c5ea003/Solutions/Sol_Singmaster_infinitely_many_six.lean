-- Prove2me | solution 1 for Singmaster.infinitely_many_six
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:24:00.169033+00:00
-- url     : https://prove2.me/submissions/c53c26d5-ec36-4a58-b2ba-ead97a07a015

-- Sol generated from Combinatorics/SingmasterFibonacci.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterFibonacci
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Theorems.Thm_Singmaster_choose_two_le_choose
import Theorems.Thm_Singmaster_six_le_mult_fib
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

theorem three_le_fib (i : ℕ) : 3 ≤ Nat.fib (2 * i + 4) := by
  have h := Nat.fib_mono (show (4 : ℕ) ≤ 2 * i + 4 by omega)
  simpa using h



/-! ## Six occurrences -/




open Singmaster in
theorem solution(M : ℕ) : ∃ t : ℕ, M < t ∧ 6 ≤ mult t := by
  refine ⟨famVal M, ?_, six_le_mult_fib M⟩
  have hd : 2 * M + 5 ≤ Nat.fib (2 * M + 5) := Nat.le_fib_self (by omega)
  have hd5 : 5 ≤ Nat.fib (2 * M + 5) := five_le_fib M
  have hc3 : 3 ≤ Nat.fib (2 * M + 4) := three_le_fib M
  have hrow : famRow M = Nat.fib (2 * M + 4) * Nat.fib (2 * M + 5) := rfl
  have hM : M < famRow M := by rw [hrow]; nlinarith
  have hcol : famCol M = Nat.fib (2 * M + 2) * Nat.fib (2 * M + 5) := rfl
  have ha1 : 1 ≤ Nat.fib (2 * M + 2) := fib_two_add_two_pos M
  have hab : Nat.fib (2 * M + 2) < Nat.fib (2 * M + 3) := fib_lt_fib_succ_of M
  have hcab : Nat.fib (2 * M + 4) = Nat.fib (2 * M + 2) + Nat.fib (2 * M + 3) :=
    Nat.fib_add_two (n := 2 * M + 2)
  have hk2 : 2 ≤ famCol M := by rw [hcol]; nlinarith
  have hb2 : 2 ≤ Nat.fib (2 * M + 3) := by omega
  have hk2n : famCol M + 2 ≤ famRow M := by
    rw [hcol, hrow, hcab]
    nlinarith
  have hval : famVal M = (famRow M).choose (famCol M) := rfl
  have hn2 : (famRow M).choose 2 ≤ famVal M := by
    rw [hval]; exact choose_two_le_choose hk2 hk2n
  have hrow15 : 15 ≤ famRow M := by rw [hrow]; nlinarith
  have h1 : famRow M * 4 ≤ famRow M * (famRow M - 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : (famRow M).choose 2 = famRow M * (famRow M - 1) / 2 := Nat.choose_two_right _
  omega
