-- Prove2me | solution 1 for FactoringLab.algebraic_barrier
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:31:30.494759+00:00
-- url     : https://prove2.me/submissions/9e120600-b5ad-4ede-ae81-08d15dc3c6c9

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
theorem solution(F : Polynomial (Polynomial ℚ))
    (h : ∀ p q : ℕ, p.Prime → q.Prime → p < q →
      (F.eval (Polynomial.C (p : ℚ))).eval ((p * q : ℕ) : ℚ) = 0) :
    F = 0 := by
  -- Step 1: for each prime `p`, the specialization `Y := p` is the zero
  -- polynomial in `ℚ[X]`, because it vanishes at the infinitely many `pq`.
  have hspec : ∀ p : ℕ, p.Prime → F.eval (Polynomial.C (p : ℚ)) = 0 := by
    intro p hp
    set H : Polynomial ℚ := F.eval (Polynomial.C (p : ℚ)) with hH
    have hroot : ∀ x ∈ (fun q : ℕ => (p : ℚ) * (q : ℚ)) '' {q : ℕ | q.Prime ∧ p < q},
        H.IsRoot x := by
      rintro x ⟨q, ⟨hq, hpq⟩, rfl⟩
      have hx : ((p * q : ℕ) : ℚ) = (p : ℚ) * (q : ℚ) := by push_cast; ring
      have := h p q hp hq hpq
      rw [hx] at this
      exact this
    have hne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    exact Polynomial.eq_zero_of_infinite_isRoot H
      (Set.Infinite.mono hroot (infinite_smul_image (infinite_primes_gt p) hne))
  -- Step 2: `F`, as a polynomial over the domain `ℚ[X]`, has the infinitely
  -- many roots `C p`.
  have hinj : Set.InjOn (fun p : ℕ => Polynomial.C ((p : ℚ))) {p : ℕ | p.Prime} := by
    intro a _ b _ hab
    have : ((a : ℚ)) = (b : ℚ) := Polynomial.C_injective hab
    exact_mod_cast this
  have hinf : {x : Polynomial ℚ | F.IsRoot x}.Infinite := by
    refine Set.Infinite.mono (s := (fun p : ℕ => Polynomial.C ((p : ℚ))) ''
      {p : ℕ | p.Prime}) ?_ (Nat.infinite_setOf_prime.image hinj)
    rintro x ⟨p, hp, rfl⟩
    exact hspec p hp
  exact Polynomial.eq_zero_of_infinite_isRoot F hinf
