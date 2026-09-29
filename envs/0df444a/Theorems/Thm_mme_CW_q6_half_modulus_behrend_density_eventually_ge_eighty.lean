-- Prove2me | Theorems.Thm_mme_CW_q6_half_modulus_behrend_density_eventually_ge_eighty
-- name    : mme_CW_q6_half_modulus_behrend_density_eventually_ge_eighty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T03:18:36.014622+00:00
-- url     : https://prove2.me/theorems/789973b7-13c1-4b7e-b0ef-3709de537153
-- title:
--   The q=6 lower-half Behrend density eventually exceeds eighty
-- statement:
--   For every sufficiently large $N$, uniformly for $0<G<N$, let
--
--   $$
--   X=\binom NG,\qquad Q=\left\lfloor\frac{4X^2+1}{2}\right\rfloor.
--   $$
--
--   Then
--
--   $$
--   80\le Q\exp\!\left(-4\sqrt{\log Q}\right).
--   $$
--
--   Consequently the explicit Behrend witness in the lower half of the q=6 hash modulus has at least eighty elements. This is the uniform positivity estimate needed before replacing a real cardinality bound by natural-number division.
-- source:
--   The explicit Behrend density bound combined with the elementary interior-binomial estimate $\binom NG\ge N$.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Sqrt

open Filter Topology

theorem mme_CW_q6_half_modulus_behrend_density_eventually_ge_eighty :
    ∀ᶠ N : ℕ in atTop,
      ∀ G : ℕ, 0 < G → G < N →
        let X : ℕ := Nat.choose N G
        let Q : ℕ := (4 * X ^ 2 + 1) / 2
        (80 : ℝ) ≤
          (Q : ℝ) * Real.exp (-4 * Real.sqrt (Real.log Q)) := by
  sorry
