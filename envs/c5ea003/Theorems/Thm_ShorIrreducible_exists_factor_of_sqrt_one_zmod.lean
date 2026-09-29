-- Prove2me | Theorems.Thm_ShorIrreducible_exists_factor_of_sqrt_one_zmod
-- name    : ShorIrreducible.exists_factor_of_sqrt_one_zmod
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T16:11:55.369257+00:00
-- url     : https://prove2.me/theorems/3ead1cfe-cd82-4455-8f74-3aa6f26190c6
-- title:
--   The same statement inside `ZMod N`: a square root of `1` other than `±1`
-- statement:
--   The same statement inside `ZMod N`: a square root of `1` other than `±1`
--   yields a nontrivial factor.
--
--   ```lean
--   theorem ShorIrreducible.exists_factor_of_sqrt_one_zmod{N : ℕ} (hN : 1 < N) (b : ZMod N)
--       (hsq : b ^ 2 = 1) (hne1 : b ≠ 1) (hne2 : b ≠ -1) :
--       ∃ d : ℕ, d ∣ N ∧ 1 < d ∧ d < N := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ShorOrderFactoring.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ShorOrderFactoring.lean#L65

-- Thm stub generated from Novelty/ShorOrderFactoring.lean
import Mathlib
import Definitions.Def_Novelty_ShorCombState

/-! # Order finding is factoring: the decisive equivalence, formalized

The assessment of the de-quantization proposal rests on the classical half of
Shor's algorithm: *a sample from the ideal QFT output distribution yields the
order `r`, and the order yields a factor of `N`.*  This file formalizes that
half, and the complementary observation that every regime in which the
tensor-network bond dimension of Shor's state is small is a regime in which the
order is found by classical search.

Main results:

* `exists_factor_of_sqrt_one` : **a nontrivial square root of `1` mod `N`
  produces a nontrivial divisor of `N`** — the classical core of Shor's
  post-processing, via `gcd(x - 1, N)`;
* `exists_factor_of_orderOf_even` : if the order `r` of `a` in `ZMod N` is
  even, positive, and `a^{r/2} ≠ -1`, then `N` has a nontrivial divisor.  So an
  order-finding oracle factors `N`;
* `exists_pow_eq_one_le_of_bondDim` : conversely, if the Shor state admits *any*
  MPS representation of bond dimension `χ` across the register cut, then
  `orderOf a ≤ χ`, hence the order is exhibited by a search of length `χ`: a
  polynomial bond dimension is a polynomial-time classical order-finding
  algorithm.  Low rank and classical easiness coincide.
-/

open Finset

open ShorIrreducible

/-! ## A nontrivial square root of one factors `N` -/

theorem ShorIrreducible.exists_factor_of_sqrt_one_zmod{N : ℕ} (hN : 1 < N) (b : ZMod N)
    (hsq : b ^ 2 = 1) (hne1 : b ≠ 1) (hne2 : b ≠ -1) :
    ∃ d : ℕ, d ∣ N ∧ 1 < d ∧ d < N := by sorry
