-- Prove2me | solution 1 for FactoringLab.rational_escape_illusory
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:55:40.023934+00:00
-- url     : https://prove2.me/submissions/3bf90ea3-f4d3-4215-9280-6402742ca58d

-- Sol generated from Probability/FactoringBarriers.lean
import Mathlib
import Definitions.Def_Probability_FactoringBarriers
/-
# Barriers I: the polynomial barrier, rational escape, holomorphic rigidity

Three of the eight barriers of the Factoring Lab framework, proved.

* `FactoringLab.polynomial_barrier` — no polynomial with rational coefficients
  computes the smaller prime factor of a semiprime.
* `FactoringLab.rational_escape_illusory` (WWW) — the same for *rational
  functions* `A/B`: passing from polynomials to quotients buys nothing.
* `FactoringLab.algebraic_barrier` — the strongest form: *no* nonzero
  polynomial relation `F(N, p) = 0` in two variables over `ℚ` holds for all
  semiprimes.  The polynomial and rational barriers are special cases.
* `FactoringLab.polynomial_barrier_counting` — a quantitative version: for a
  fixed small factor `p`, a polynomial of degree `d` can return the correct
  factor at no more than `d` semiprimes `pq`.
* `FactoringLab.holomorphic_rigidity` / `holomorphic_rigidity_barrier` (HRB) —
  an entire function that reproduces the reciprocal of the smaller prime factor
  at the reciprocals of semiprimes is forced by the identity theorem to be
  constant, which is impossible.

The proofs share one mechanism: fixing the small factor makes the sample set
accumulate (at infinity for polynomials, at `0` for the holomorphic version),
and rigidity of the function class then forces a constant, which two different
choices of the small factor contradict.
-/

open FactoringLab

open Polynomial Filter Set

/-! ### Arithmetic input: infinitely many primes above any bound -/

/-- There are infinitely many primes exceeding any given bound. -/
theorem infinite_primes_gt (m : ℕ) : {q : ℕ | q.Prime ∧ m < q}.Infinite := by
  have h : ({q : ℕ | q.Prime} \ {q : ℕ | q ≤ m}).Infinite :=
    Nat.infinite_setOf_prime.diff (Set.finite_Iic m)
  refine h.mono ?_
  intro q hq
  exact ⟨hq.1, lt_of_not_ge (fun hle => hq.2 hle)⟩

/-- Scaling an infinite set of naturals by a nonzero rational keeps it infinite
inside `ℚ`. -/
theorem infinite_smul_image {S : Set ℕ} (hS : S.Infinite) {c : ℚ} (hc : c ≠ 0) :
    ((fun q : ℕ => c * (q : ℚ)) '' S).Infinite := by
  refine hS.image ?_
  intro a _ b _ hab
  have : (a : ℚ) = b := mul_left_cancel₀ hc hab
  exact_mod_cast this

/-! ### The polynomial and rational barriers -/




/-! ### The algebraic barrier: no algebraic relation between `N` and `p` -/




/-! ### Holomorphic rigidity -/










open FactoringLab in
theorem solution(A B : Polynomial ℚ) :
    ¬ ∀ p q : ℕ, p.Prime → q.Prime → p < q →
        B.eval ((p * q : ℕ) : ℚ) ≠ 0 ∧
          A.eval ((p * q : ℕ) : ℚ) = (p : ℚ) * B.eval ((p * q : ℕ) : ℚ) := by
  intro h
  -- The polynomial `A - 3•B` vanishes at `3q` for every prime `q > 3`.
  set C : Polynomial ℚ := A - Polynomial.C 3 * B with hC
  have hroot : ∀ x ∈ (fun q : ℕ => (3 : ℚ) * (q : ℚ)) '' {q : ℕ | q.Prime ∧ 3 < q},
      C.IsRoot x := by
    rintro x ⟨q, ⟨hq, hq3⟩, rfl⟩
    have h3 : Nat.Prime 3 := by norm_num
    have := (h 3 q h3 hq hq3).2
    have hcast : (((3 * q : ℕ) : ℚ)) = (3 : ℚ) * (q : ℚ) := by push_cast; ring
    rw [hcast] at this
    simp only [hC, IsRoot, eval_sub, eval_mul, eval_C]
    rw [this]
    push_cast
    ring
  have hinf : {x : ℚ | C.IsRoot x}.Infinite := by
    refine Set.Infinite.mono hroot ?_
    exact infinite_smul_image (infinite_primes_gt 3) (by norm_num)
  have hC0 : C = 0 := Polynomial.eq_zero_of_infinite_isRoot C hinf
  -- Hence `A = 3B` identically, contradicting the value at `N = 35 = 5 * 7`.
  have hAB : ∀ x : ℚ, A.eval x = 3 * B.eval x := by
    intro x
    have : C.eval x = 0 := by rw [hC0]; simp
    simp only [hC, eval_sub, eval_mul, eval_C, sub_eq_zero] at this
    exact this
  have h5 : Nat.Prime 5 := by norm_num
  have h7 : Nat.Prime 7 := by norm_num
  obtain ⟨hne, heq⟩ := h 5 7 h5 h7 (by norm_num)
  rw [hAB] at heq
  have : (2 : ℚ) * B.eval ((5 * 7 : ℕ) : ℚ) = 0 := by push_cast at heq ⊢; linarith
  have : B.eval ((5 * 7 : ℕ) : ℚ) = 0 := by linarith
  exact hne this
