-- Prove2me | solution 1 for Singmaster.six_le_mult_fib
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:15:34.55365+00:00
-- url     : https://prove2.me/submissions/f203c59f-b346-4fc0-9a3c-3162fb3346b5

-- Sol generated from Combinatorics/SingmasterFibonacci.lean
import Mathlib
import Definitions.Def_Combinatorics_SingmasterFibonacci
import Definitions.Def_Combinatorics_SingmasterOccurrences
import Theorems.Thm_Singmaster_choose_cross
import Theorems.Thm_Singmaster_choose_two_le_choose
import Theorems.Thm_Singmaster_fib_cross
import Theorems.Thm_Singmaster_mem_occ
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
theorem solution(i : ℕ) : 6 ≤ mult (famVal i) := by
  classical
  set a := Nat.fib (2 * i + 2) with ha
  set b := Nat.fib (2 * i + 3) with hb
  set c := Nat.fib (2 * i + 4) with hc
  set d := Nat.fib (2 * i + 5) with hd
  have hcab : c = a + b := Nat.fib_add_two (n := 2 * i + 2)
  have ha1 : 1 ≤ a := fib_two_add_two_pos i
  have hab : a < b := fib_lt_fib_succ_of i
  have hd5 : 5 ≤ d := five_le_fib i
  have hc3 : 3 ≤ c := three_le_fib i
  set n := famRow i with hn
  set k := famCol i with hk
  have hrow : n = c * d := rfl
  have hcol : k = a * d := rfl
  have hnk : n - k = b * d := by
    show c * d - a * d = b * d
    rw [hcab, Nat.add_mul]
    omega
  -- basic size estimates
  have hk5 : 5 ≤ k := by rw [hcol]; nlinarith
  have hbd : k + 3 < n - k := by
    rw [hnk, hcol]
    nlinarith
  have hkn : k ≤ n := by omega
  have hn15 : 15 ≤ n := by rw [hrow]; nlinarith
  -- the value and its size
  set t := famVal i with ht
  have htval : t = n.choose k := rfl
  have hn2 : n.choose 2 ≤ t := by rw [htval]; exact choose_two_le_choose (by omega) (by omega)
  have hnt : n < t := by
    have h1 : n * 4 ≤ n * (n - 1) := Nat.mul_le_mul_left n (by omega)
    have h2 : n.choose 2 = n * (n - 1) / 2 := Nat.choose_two_right n
    omega
  have ht3 : 3 ≤ t := by omega
  -- the cross-row repetition
  have hcross : n.choose k = (n - 1).choose (k + 1) := by
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hjm : j + (n - k) + 1 = n := by omega
    have hjm' : j + (n - k) = n - 1 := by omega
    have hdio : (j + (n - k) + 1) * (j + 2) = (n - k) * ((n - k) - 1) := by
      have hfc := fib_cross i
      rw [← hn, ← hk] at hfc
      rw [hjm, show j + 2 = k + 1 by omega]
      exact hfc
    have := choose_cross (j := j) (m := n - k) (by omega) hdio
    rw [hjm, hjm'] at this
    rw [hj]
    exact this
  -- the six positions
  have m1 : (t, 1) ∈ occ t := mem_occ (by omega) (by omega) (Nat.choose_one_right t)
  have m2 : (t, t - 1) ∈ occ t := by
    refine mem_occ (by omega) (by omega) ?_
    have h := Nat.choose_symm (n := t) (k := 1) (by omega)
    rw [Nat.choose_one_right] at h
    exact h
  have m3 : (n, k) ∈ occ t := mem_occ (by omega) (by omega) htval.symm
  have m4 : (n, n - k) ∈ occ t :=
    mem_occ (by omega) (by omega) (by rw [Nat.choose_symm hkn]; exact htval.symm)
  have m5 : (n - 1, k + 1) ∈ occ t :=
    mem_occ (by omega) (by omega) (by rw [← hcross]; exact htval.symm)
  have m6 : (n - 1, n - k - 2) ∈ occ t := by
    refine mem_occ (by omega) (by omega) ?_
    have hs : (n - 1).choose (n - 1 - (k + 1)) = (n - 1).choose (k + 1) :=
      Nat.choose_symm (by omega)
    rw [show n - k - 2 = n - 1 - (k + 1) by omega, hs, ← hcross]
    exact htval.symm
  have hsub : ({(t, 1), (t, t - 1), (n, k), (n, n - k), (n - 1, k + 1), (n - 1, n - k - 2)} :
      Finset (ℕ × ℕ)) ⊆ occ t := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨m1, m2, m3, m4, m5, m6⟩
  have hcard : ({(t, 1), (t, t - 1), (n, k), (n, n - k), (n - 1, k + 1), (n - 1, n - k - 2)} :
      Finset (ℕ × ℕ)).card = 6 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega),
      Finset.card_insert_of_notMem (by
        simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega),
      Finset.card_insert_of_notMem (by
        simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega),
      Finset.card_insert_of_notMem (by
        simp only [mem_insert, mem_singleton, Prod.mk.injEq]; omega),
      Finset.card_insert_of_notMem (by
        simp only [mem_singleton, Prod.mk.injEq]; omega),
      Finset.card_singleton]
  calc 6 = _ := hcard.symm
    _ ≤ mult t := card_le_card hsub
