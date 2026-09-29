-- Prove2me | solution 1 for WolframGrothendieck.eq_imp_pow2
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:16:39.451753+00:00
-- url     : https://prove2.me/submissions/1d5d034b-51ad-4744-ac5b-7a0424be789d

-- Sol generated from Novelty/CANilpotencyScheme.lean
import Mathlib
import Definitions.Def_Novelty_CANilpotencyScheme

/-!
# Nilpotency of Additive Cellular Automata on Cyclic Lattices: Wolfram meets Grothendieck

This file proves a **cross-domain bridge** connecting three areas that, on their
face, look unrelated:

* **Cellular automata / discrete dynamics** — Wolfram's additive elementary
  cellular automata (the `Rule 60` / `Rule 90` family) on a *finite cyclic*
  lattice `ℤ/n`.
* **Commutative algebra & algebraic geometry** — the coordinate ring of the
  finite group scheme `μₙ` of `n`-th roots of unity over `𝔽₂`, realised as the
  quotient ring `𝔽₂[X]/(Xⁿ − 1)`, and the *nilpotency* of a distinguished ring
  element (equivalently, whether the scheme `μₙ` is infinitesimal / non-reduced).
* **Elementary number theory** — the arithmetic of powers of `2`.

## The dictionary

A spatially `n`-periodic binary configuration `s : ℤ/n → 𝔽₂` is encoded as an
element of the group algebra `𝔽₂[ℤ/n] ≅ 𝔽₂[X]/(Xⁿ − 1)` (send the cell at
position `i` to the monomial `Xⁱ`).  The *additive* nearest-neighbour rule
"`new cell = old cell + right neighbour`" (an `𝔽₂`-linear elementary CA) is then
exactly **multiplication by the ring element `1 + X`**.  Time-`t` evolution is
multiplication by `(1 + X)ᵗ`, so the whole space-time behaviour is governed by
the powers of one element `u = 1 + X` in the finite ring
`Rq n = 𝔽₂[X]/(Xⁿ − 1)`.

The automaton is **nilpotent** — every configuration dies to the all-zero state
in finitely many steps — **iff** the ring element `u` is nilpotent, i.e. `uᴺ = 0`
for some `N`.

## Main theorem

`caUnit_isNilpotent_iff` :  for `n > 0`,

  `IsNilpotent (caUnit n)  ↔  ∃ k, n = 2 ^ k`.

Equivalently (`ca_dies_iff_pow2`): *every* configuration reaches `0` under the
rule iff the lattice size is a power of two.

This is the "Wolfram meets Grothendieck" statement: the additive CA on `ℤ/n`
collapses to nothing precisely when the affine group scheme `μₙ = Spec 𝔽₂[X]/(Xⁿ−1)`
is a **fat point** (non-reduced, purely infinitesimal), which over `𝔽₂` happens
exactly when `n` is a power of the characteristic `2`.  The dynamical fact
(everything dies) is thus equivalent to a purely arithmetic fact (`n = 2ᵏ`).

## Proof architecture

* `caUnit_isNilpotent_iff_dvd` — nilpotency in the quotient ring is the
  divisibility statement `∃ N, (Xⁿ − 1) ∣ (X + 1)ᴺ`.
* `pow2_imp_eq` — if `n = 2ᵏ` then `Xⁿ − 1 = (X + 1)ⁿ` (the Frobenius /
  "freshman's dream" collapse `(X+1)^{2ᵏ} = X^{2ᵏ} + 1`).
* `dvd_imp_eq` — conversely, since `X + 1` is *prime* in `𝔽₂[X]`, any divisor of
  a power of `X + 1` is a power of `X + 1`; matching monic degrees forces
  `Xⁿ − 1 = (X + 1)ⁿ`.
* `eq_imp_pow2` — the arithmetic heart: `Xⁿ − 1 = (X + 1)ⁿ ⟹ n = 2ᵏ`, proved by
  strong induction using char-2 square-root injectivity (`sq_inj`) and a
  derivative/`eval 0` parity computation (`even_of_eq`).

All results live over `𝔽₂ = ZMod 2` with polynomials in `Polynomial (ZMod 2)`.
-/

open Polynomial

noncomputable section

open WolframGrothendieck

/-! ## Char-2 polynomial toolbox -/

/-- **Squaring is injective** in `𝔽₂[X]` (a domain of characteristic `2`):
`A² = B² → A = B`, because `(A+B)² = A² + B²` collapses. -/
theorem sq_inj (A B : (ZMod 2)[X]) (h : A ^ 2 = B ^ 2) : A = B := by
  have hz : (A + B) ^ 2 = 0 := by rw [add_pow_char, h]; exact CharTwo.add_self_eq_zero _
  have h2 : A + B = 0 := (pow_eq_zero_iff (by norm_num)).mp hz
  have : A = -B := by linear_combination h2
  rw [this, CharTwo.neg_eq]

/-- Char-2 "square = double frequency": `(Xᵐ − 1)² = X^{2m} − 1`. -/
theorem sq_Xpow_sub (m : ℕ) : (X ^ m - 1 : (ZMod 2)[X]) ^ 2 = X ^ (2 * m) - 1 := by
  have e1 : (X ^ m - 1 : (ZMod 2)[X]) = X ^ m + 1 := by rw [sub_eq_add_neg, CharTwo.neg_eq]
  have e2 : (X ^ (2 * m) - 1 : (ZMod 2)[X]) = X ^ (2 * m) + 1 := by
    rw [sub_eq_add_neg, CharTwo.neg_eq]
  rw [e1, e2, add_pow_char, one_pow, ← pow_mul, mul_comm m 2]


/-! ## The three key implications -/


/-- **Parity from the derivative.** If `Xⁿ − 1 = (X + 1)ⁿ` with `n ≥ 2`, then `n`
is even: differentiate and evaluate at `0`, giving `n · 0 = n · 1` in `𝔽₂`. -/
theorem even_of_eq (n : ℕ) (hn : 2 ≤ n)
    (h : (X ^ n - 1 : (ZMod 2)[X]) = (X + 1) ^ n) : (n : ZMod 2) = 0 := by
  have hd := congrArg derivative h
  simp only [derivative_sub, derivative_one, sub_zero,
    derivative_pow, derivative_add, derivative_X, add_zero, mul_one] at hd
  have he := congrArg (eval 0) hd
  rw [eval_mul, eval_mul, eval_pow, eval_pow, eval_X, eval_add, eval_X, eval_one] at he
  simp only [zero_add, one_pow, mul_one] at he
  rw [show (0 : ZMod 2) ^ (n - 1) = 0 by exact zero_pow (by omega)] at he
  rw [mul_zero, eq_comm] at he
  simpa using he



/-! ## The cellular automaton as an element of a finite ring -/






/-! ## Main bridge theorem -/



/-! ## Concrete instances -/






open WolframGrothendieck in
theorem solution(n : ℕ) (hn : 0 < n)
    (heq : (X ^ n - 1 : (ZMod 2)[X]) = (X + 1) ^ n) : ∃ k, n = 2 ^ k := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · interval_cases n
      · exact ⟨0, rfl⟩
    · have hev := even_of_eq n h2 heq
      have hdvd : 2 ∣ n := Fin.natCast_eq_zero.mp hev
      obtain ⟨m, rfl⟩ := hdvd
      have hm : 0 < m := by omega
      have hmlt : m < 2 * m := by omega
      have hred : (X ^ m - 1 : (ZMod 2)[X]) = (X + 1) ^ m := by
        apply sq_inj
        rw [sq_Xpow_sub, ← pow_mul, mul_comm m 2, heq]
      obtain ⟨k, hk⟩ := ih m hmlt hm hred
      exact ⟨k + 1, by rw [hk, pow_succ, mul_comm]⟩
