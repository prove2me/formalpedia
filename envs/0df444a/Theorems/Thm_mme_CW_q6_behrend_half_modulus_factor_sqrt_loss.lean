-- Prove2me | Theorems.Thm_mme_CW_q6_behrend_half_modulus_factor_sqrt_loss
-- name    : mme_CW_q6_behrend_half_modulus_factor_sqrt_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T19:26:01.862537+00:00
-- url     : https://prove2.me/theorems/1a8a4033-2d5e-4399-9113-4f4af0ba891b
-- title:
--   Behrend density absorbs fixed q=6 hashing and polynomial losses
-- statement:
--   Fix a nonnegative integer $d$. There is a constant $C\ge0$ such that, for all sufficiently large $N$ and every $G\le N$, if
--
--   $$
--   X=\binom NG,\qquad M=4X^2+1,
--   $$
--
--   then the lower half of the odd modulus contains a nonempty three-term-progression-free set $S\subseteq\{0,\ldots,\lfloor M/2\rfloor-1\}$ for which
--
--   $$
--   e^{-C\sqrt{N+1}}\le \frac{(|S|/M)^d}{(N+1)^d}.
--   $$
--
--   Thus every fixed number of Behrend-density factors and every fixed polynomial pruning loss are jointly subexponential on the square-root scale required by the coupled $q=6$ hash. The interval is deliberately the lower half of $M$, so later modular equalities have an ordinary-integer no-wrap interpretation.
-- source:
--   Explicit finite Behrend witness: Prove2Me theorem mme_behrend_explicit_threeAP_free, cb45e6ba-b86a-4119-a08e-f162c8fbc86b. Hash modulus and lower-half no-wrap role: D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal p. 271; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Sqrt
import Theorems.Thm_mme_behrend_explicit_threeAP_free

open Filter Topology

theorem mme_CW_q6_behrend_half_modulus_factor_sqrt_loss (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop,
        ∀ G : ℕ, G ≤ N →
          let Xcount : ℕ := Nat.choose N G
          let Mmod : ℕ := 4 * Xcount ^ 2 + 1
          ∃ S : Finset ℕ,
            S ⊆ Finset.range (Mmod / 2) ∧
            ThreeAPFree (S : Set ℕ) ∧
            0 < S.card ∧
            Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
              (((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                (((N + 1 : ℕ) : ℝ) ^ d) := by sorry
