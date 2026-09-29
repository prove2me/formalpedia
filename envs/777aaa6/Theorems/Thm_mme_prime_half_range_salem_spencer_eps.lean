-- Prove2me | Theorems.Thm_mme_prime_half_range_salem_spencer_eps
-- name    : mme_prime_half_range_salem_spencer_eps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-18T13:38:18.343871+00:00
-- url     : https://prove2.me/theorems/077825db-4829-4797-8798-b5e0da17ea39
-- title:
--   Prime moduli with near-linear progression-free half-range sets
-- statement:
--   For every real $\varepsilon>0$, there is an integer threshold $B_0$ such that, for every integer $B\ge B_0$, one can choose an odd prime $p>8$ and a nonempty finite set $S$ satisfying
--   $$
--   B<p\le 2B,\qquad
--   S\subseteq\{0,\ldots,\lfloor p/2\rfloor-1\},\qquad
--   |S|\ge p^{1-\varepsilon}.
--   $$
--   The set $S$ contains no nontrivial three-term arithmetic progression: if $a,b,c\in S$ and $a+c=2b$, then $a=b=c$.
--
--   Thus the modulus exceeds any prescribed sufficiently large threshold by at most a factor of two, while its permitted half-range contains a progression-free set with an arbitrarily small power loss. The theorem constructs the prime and the set; neither existence is assumed. It does not provide bounds on tensor-family degrees or establish a matrix-multiplication exponent.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5 , Section 3.8 Theorem 3.8 and Section 3.10 (Salem–Spencer hashing). Derived parameter-choice lemma, not a verbatim numbered theorem. Uses the proved epsilon-form of Behrend's bound mme_salem_spencer_eps_form (58665074-3139-4a77-90ef-283481f2a278) and Mathlib Nat.exists_prime_lt_and_le_two_mul (Bertrand's postulate), https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Bertrand.html . The half-range formulation prevents wraparound in modular progression tests.

import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic

set_option autoImplicit false

theorem mme_prime_half_range_salem_spencer_eps (ε : ℝ) (hε : 0 < ε) :
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ 8 < p ∧ B < p ∧ p ≤ 2 * B ∧
        ∃ S : Finset ℕ, S ⊆ Finset.range (p / 2) ∧
          ThreeAPFree (S : Set ℕ) ∧ 0 < S.card ∧
          (p : ℝ) ^ (1 - ε) ≤ (S.card : ℝ) := by sorry
