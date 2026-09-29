-- Prove2me | Theorems.Thm_WolframGrothendieck_eq_imp_pow2
-- name    : WolframGrothendieck.eq_imp_pow2
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:41:19.74214+00:00
-- url     : https://prove2.me/theorems/9b66de9e-eb56-4c05-a9d5-390ecfc2397d
-- title:
--   Arithmetic heart.
-- statement:
--   **Arithmetic heart.** `Xⁿ − 1 = (X + 1)ⁿ ⟹ n = 2ᵏ`.  Strong induction: the
--   odd `n ≥ 2` case is killed by `even_of_eq`; the even case `n = 2m` is reduced to
--   `m` via char-2 square-root injectivity, since `(Xᵐ − 1)² = X^{2m} − 1` and
--   `((X+1)ᵐ)² = (X+1)^{2m}`.
--
--   ```lean
--   theorem WolframGrothendieck.eq_imp_pow2(n : ℕ) (hn : 0 < n)
--       (heq : (X ^ n - 1 : (ZMod 2)[X]) = (X + 1) ^ n) : ∃ k, n = 2 ^ k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/CANilpotencyScheme.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/CANilpotencyScheme.lean#L115

-- Thm stub generated from Novelty/CANilpotencyScheme.lean
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




/-! ## The three key implications -/

theorem WolframGrothendieck.eq_imp_pow2(n : ℕ) (hn : 0 < n)
    (heq : (X ^ n - 1 : (ZMod 2)[X]) = (X + 1) ^ n) : ∃ k, n = 2 ^ k := by sorry
