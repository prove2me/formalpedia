-- Prove2me | solution 1 for FibonacciApparitionSheaf.exists_pos_dvd_fib
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:01:44.50043+00:00
-- url     : https://prove2.me/submissions/a5927d9c-2db1-4f5a-b5c4-1b0e4c11c8cb

-- Sol generated from Algebra/PosetTheory/FibonacciApparitionSheaf.lean
import Mathlib
import Definitions.Def_Algebra_PosetTheory_FibonacciApparitionSheaf

/-!
# The Fibonacci rank of apparition

For a modulus `p ≥ 1`, the *rank of apparition* (entry point) of `p` is the least positive
index `n` with `p ∣ F n`.  This file provides the general theory used by the Carmichael and
primitive-divisor developments:

* `exists_pos_dvd_fib` — every positive modulus divides some Fibonacci number of positive
  index.  The proof is the classical pigeonhole argument: the pair `(F n, F (n+1))` mod `p`
  takes finitely many values, and the Fibonacci recursion can be run backwards, so the
  initial pair `(0, 1)` recurs.
* `fibRank` — the rank of apparition, defined by `Nat.find` when it exists and `0`
  otherwise, so that it is a total function.
* `fibRank_pos`, `dvd_fib_fibRank`, `fibRank_min` — its defining properties.
* `fibRank_dvd_iff` — the *strong divisibility* characterisation `p ∣ F n ↔ fibRank p ∣ n`,
  a consequence of `Nat.fib_gcd`.
-/

open FibonacciApparitionSheaf











open FibonacciApparitionSheaf in
theorem solution(p : ℕ) (hp : 0 < p) : ∃ k, 0 < k ∧ p ∣ Nat.fib k := by
  haveI : NeZero p := ⟨hp.ne'⟩
  set T : ℕ → ZMod p × ZMod p :=
    fun n => ((Nat.fib n : ZMod p), (Nat.fib (n + 1) : ZMod p)) with hT
  -- running the recursion backwards
  have hstep : ∀ i j : ℕ, T (i + 1) = T (j + 1) → T i = T j := by
    intro i j h
    have h1 : (Nat.fib (i + 1) : ZMod p) = (Nat.fib (j + 1) : ZMod p) := congrArg Prod.fst h
    have h2 : (Nat.fib (i + 2) : ZMod p) = (Nat.fib (j + 2) : ZMod p) := congrArg Prod.snd h
    have e1 : Nat.fib (i + 2) = Nat.fib i + Nat.fib (i + 1) := Nat.fib_add_two
    have e2 : Nat.fib (j + 2) = Nat.fib j + Nat.fib (j + 1) := Nat.fib_add_two
    rw [e1, e2] at h2
    push_cast at h2
    have hfib : (Nat.fib i : ZMod p) = (Nat.fib j : ZMod p) := by
      rw [h1] at h2
      exact add_right_cancel h2
    exact Prod.ext hfib h1
  have hshift : ∀ i d : ℕ, T i = T (i + d) → T 0 = T d := by
    intro i
    induction i with
    | zero => intro d h; simpa using h
    | succ i ih =>
        intro d h
        refine ih d (hstep i (i + d) ?_)
        simpa [Nat.succ_add, Nat.add_right_comm] using h
  obtain ⟨i, j, hij, hEq⟩ := Finite.exists_ne_map_eq_of_infinite T
  rcases Nat.lt_or_ge i j with hlt | hge
  · have hd : T i = T (i + (j - i)) := by
      rw [show i + (j - i) = j by omega]; exact hEq
    have h0 := hshift i (j - i) hd
    refine ⟨j - i, by omega, ?_⟩
    have hzero : (Nat.fib (j - i) : ZMod p) = 0 := by
      have hfst := congrArg Prod.fst h0
      simp [hT] at hfst
      simpa using hfst.symm
    exact (ZMod.natCast_eq_zero_iff _ _).mp hzero
  · have hji : j < i := by
      rcases Nat.lt_or_ge j i with h | h
      · exact h
      · exact absurd (le_antisymm hge h) hij.symm
    have hd : T j = T (j + (i - j)) := by
      rw [show j + (i - j) = i by omega]; exact hEq.symm
    have h0 := hshift j (i - j) hd
    refine ⟨i - j, by omega, ?_⟩
    have hzero : (Nat.fib (i - j) : ZMod p) = 0 := by
      have hfst := congrArg Prod.fst h0
      simp [hT] at hfst
      simpa using hfst.symm
    exact (ZMod.natCast_eq_zero_iff _ _).mp hzero
