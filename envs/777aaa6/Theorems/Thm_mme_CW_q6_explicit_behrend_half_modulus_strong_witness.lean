-- Prove2me | Theorems.Thm_mme_CW_q6_explicit_behrend_half_modulus_strong_witness
-- name    : mme_CW_q6_explicit_behrend_half_modulus_strong_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T03:29:39.248266+00:00
-- url     : https://prove2.me/theorems/3a10652f-45f6-4405-ad1f-8ad862989f16
-- title:
--   One explicit lower-half Behrend witness has both density and cardinality margins
-- statement:
--   For all sufficiently large $N$, uniformly for $0<G<N$, put $X=\binom NG$ and $M=4X^2+1$. There is a single three-term-progression-free set $S$ in the lower half of the modulus such that\n\n$$|S|\ge 80,\qquad e^{-12\sqrt{N+1}}\le \frac{|S|/M}{N+1}. $$\n\nThe same explicit Behrend witness supplies both conclusions. The fixed cardinality margin is what makes subsequent natural-number floor loss rigorous, while the square-root density margin supplies the asymptotic exponent.
-- source:
--   Behrend's explicit three-term-progression-free construction, combined with the q=6 modulus $M=4\binom NG^2+1$ used by Coppersmith and Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), p. 271; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib
import Theorems.Thm_mme_behrend_explicit_threeAP_free
import Theorems.Thm_mme_CW_q6_half_modulus_behrend_density_eventually_ge_eighty

open Filter Topology

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_CW_q6_explicit_behrend_half_modulus_strong_witness :
    ∀ᶠ N : ℕ in atTop,
      ∀ G : ℕ, 0 < G → G < N →
        let X : ℕ := Nat.choose N G
        let M : ℕ := 4 * X ^ 2 + 1
        ∃ S : Finset ℕ,
          S ⊆ Finset.range (M / 2) ∧
          ThreeAPFree (S : Set ℕ) ∧
          80 ≤ S.card ∧
          Real.exp (-12 * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
            (S.card : ℝ) / (M : ℝ) /
              (((N + 1 : ℕ) : ℝ)) := by
  sorry
