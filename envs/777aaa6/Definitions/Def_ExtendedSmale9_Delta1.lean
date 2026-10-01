-- Prove2me | Definitions.Def_ExtendedSmale9_Delta1
-- name    : ExtendedSmale9_Delta1
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-30T13:54:56.565204+00:00
-- url     : https://prove2.me/theorems/1b9ee160-6514-4833-9ad4-227f795a395c
-- title:
--   $\Delta_1$-information and the problem $\{\Xi,\Omega,M,\Lambda\}^{\Delta_1}$ (Def. 9.12, 9.14)
-- statement:
--   Let $D_n = \{k2^{-n}: k\in\mathbb Z\}$.
--
--   A family $\hat f_{j,n}:\Omega\to D_n+iD_n$ ($n = 1,2,\dots$) **provides $\Delta_1$-information** for $\Lambda$, written $\hat\Lambda\in L^1(\Lambda)$ (Definition 9.12), if $|\hat f_{j,n}(\iota)-\Lambda_j(\iota)|\le 2^{-n}$ for all $j$, $n$ and $\iota$ (display (9.8)). The problem $\{\Xi,\Omega,M,\hat\Lambda\}$ has the evaluations $\hat f_{j,n}$.
--
--   The **computational problem with $\Delta_1$-information** (Definition 9.14) has as inputs all oracle families $\tilde\iota = (\tilde\iota_{j,n})$ with $\tilde\iota_{j,n}\in D_n+iD_n$ and $|\tilde\iota_{j,n}-\Lambda_j(\iota)|\le2^{-n}$ for some $\iota\in\Omega$. Its evaluations are $\tilde f_{j,n}(\tilde\iota)=\tilde\iota_{j,n}$ and its solution map is $\tilde\Xi(\tilde\iota)=\Xi(\iota)$. In Lean an input is stored as the pair $(\iota,\tilde\iota)$, and algorithms only read $\tilde\iota$.
-- source:
--   A. Bastounis, A. C. Hansen, V. Vlačić, *The extended Smale's 9th problem — On computational barriers and paradoxes in estimation, regularisation, computer-assisted proofs, and learning* (preprint, 126 pp., version of 28 Jan 2021), §9.3, display (9.8), Definition 9.12 and Definition 9.14 (pp. 23–24).

import Mathlib

/-!
# ∆₁-information

Bastounis–Hansen–Vlačić, *The extended Smale's 9th problem*, §9.3:
the dyadic sets `D_n = {k 2^{-n} | k ∈ ℤ}`, display (9.8), Definition 9.12
(∆₁-information, the family `L¹(Λ)`) and Definition 9.14 (the computational problem
with ∆₁-information `{Ξ, Ω, M, Λ}^{∆₁}`).  Accuracy levels `n` range over `ℕ+ = {1, 2, …}`.
-/

namespace ExtendedSmale9

/-- `z ∈ D_n + i D_n`: both the real and imaginary parts of `z` are of the form
`k / 2^n` with `k ∈ ℤ`. -/
def IsDyadic (n : ℕ) (z : ℂ) : Prop :=
  (∃ k : ℤ, z.re = (k : ℝ) / 2 ^ n) ∧ ∃ k : ℤ, z.im = (k : ℝ) / 2 ^ n

/-- Definition 9.12: the family `fhat j n : Ω → D_n + i D_n` provides ∆₁-information for
the evaluation family `Λ`, i.e. `fhat ∈ L¹(Λ)`: each `fhat j n ι` is a dyadic of level `n`
and `sup_j |fhat j n ι - Λ j ι| ≤ 2^{-n}` for every `ι` (display (9.8)). -/
def IsDelta1Info {Ω Idx : Type*} (Λ : Idx → Ω → ℂ) (fhat : Idx → ℕ+ → Ω → ℂ) : Prop :=
  ∀ j (n : ℕ+) ι, IsDyadic (n : ℕ) (fhat j n ι) ∧ ‖fhat j n ι - Λ j ι‖ ≤ 1 / 2 ^ (n : ℕ)

/-- The evaluation family `Λ̂ = {fhat j n}` of the computational problem `{Ξ, Ω, M, Λ̂}`,
indexed by pairs `(j, n)`. -/
def delta1Eval {Ω Idx : Type*} (fhat : Idx → ℕ+ → Ω → ℂ) : Idx × ℕ+ → Ω → ℂ :=
  fun jn ι => fhat jn.1 jn.2 ι

/-- Definition 9.14: the input set `Ω̃` of `{Ξ, Ω, M, Λ}^{∆₁}`.  An element is a pair
`(ι, ι̃)` of an input `ι ∈ Ω` together with an arbitrary oracle sequence
`ι̃ = (ι̃ j n)_{j, n}` with `ι̃ j n ∈ D_n + i D_n` and `|ι̃ j n - Λ j ι| ≤ 2^{-n}`.
(The input `ι` is the one that `ι̃` corresponds to; it is only used to define the
solution map `Ξ̃(ι̃) = Ξ(ι)`, since algorithms can only read `ι̃`.) -/
def Delta1Input {Ω Idx : Type*} (Λ : Idx → Ω → ℂ) : Type _ :=
  {q : Ω × (Idx → ℕ+ → ℂ) //
    ∀ j (n : ℕ+), IsDyadic (n : ℕ) (q.2 j n) ∧ ‖q.2 j n - Λ j q.1‖ ≤ 1 / 2 ^ (n : ℕ)}

/-- Definition 9.14: the evaluation family `Λ̃ = {f̃_{j,n}}` on `Ω̃`, `f̃_{j,n}(ι̃) = ι̃ j n`. -/
def delta1InputEval {Ω Idx : Type*} (Λ : Idx → Ω → ℂ) : Idx × ℕ+ → Delta1Input Λ → ℂ :=
  fun jn q => q.1.2 jn.1 jn.2

/-- The input `ι ∈ Ω` to which an oracle input `ι̃ ∈ Ω̃` corresponds. -/
def Delta1Input.input {Ω Idx : Type*} {Λ : Idx → Ω → ℂ} (q : Delta1Input Λ) : Ω := q.1.1

end ExtendedSmale9


