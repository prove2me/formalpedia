-- Prove2me | Theorems.Thm_mme_prime_half_modulus_behrend
-- name    : mme_prime_half_modulus_behrend
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T21:06:37.515789+00:00
-- url     : https://prove2.me/theorems/9e8ad765-41cd-4474-9172-ac31111857db
-- title:
--   A prime lower-half interval contains an explicit Behrend set
-- statement:
--   For every positive integer $Q$, there is a prime $p$ with
--
--   $$
--   2Q<p\le4Q
--   $$
--
--   and a three-term-progression-free set $S$ contained in the lower half $\{0,\ldots,\lfloor p/2\rfloor-1\}$ of the modulus such that
--
--   $$
--   |S|\ge Q\exp\bigl(-4\sqrt{\log Q}\bigr).
--   $$
--
--   The prime comes from Bertrand's postulate, and the set is the explicit Behrend witness on the initial interval of length $Q$. The lower-half placement ensures that modular three-term progressions do not wrap around, which is the form needed by Coppersmith--Winograd affine hashing.
-- source:
--   F. A. Behrend, On sets of integers which contain no three terms in arithmetical progression, Proc. Natl. Acad. Sci. USA 32 (1946), 331--332; Bertrand's postulate; combined for the hashing step of D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 267--271; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.NumberTheory.Bertrand
import Theorems.Thm_mme_behrend_explicit_threeAP_free

open Real

theorem mme_prime_half_modulus_behrend (Q : ℕ) (hQ : 0 < Q) :
    ∃ p : ℕ, Nat.Prime p ∧ 2 * Q < p ∧ p ≤ 4 * Q ∧
      ∃ S : Finset ℕ,
        S ⊆ Finset.range (p / 2) ∧
        ThreeAPFree (S : Set ℕ) ∧
        (Q : ℝ) * Real.exp (-4 * Real.sqrt (Real.log Q)) ≤
          (S.card : ℝ) := by
  sorry
