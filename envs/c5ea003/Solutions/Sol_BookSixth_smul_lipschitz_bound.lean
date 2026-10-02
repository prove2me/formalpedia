-- Prove2me | solution 1 for BookSixth.smul_lipschitz_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T09:37:08.079736+00:00
-- url     : https://prove2.me/submissions/47849fab-6c53-4e39-a410-36414be16a7e

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

/-- A scalar `c`-Lipschitz function times a bounded `M`-Lipschitz function is
`(c * M + C * L)`-Lipschitz, where `C` bounds the scalar function.

No sign hypotheses are required: the two difference hypotheses, evaluated at
any two points, force `0 ≤ c` and `0 ≤ L`, and the pointwise bounds force
`0 ≤ M` and `0 ≤ C`. -/
theorem solution {c M C L : ℝ}
    (chi : Space3 → ℝ) (D : Space3 → Space3)
    (hchi : ∀ x y : Space3, |chi x - chi y| ≤ c * ‖x - y‖)
    (hchiC : ∀ x : Space3, |chi x| ≤ C)
    (hDM : ∀ x : Space3, ‖D x‖ ≤ M)
    (hD : ∀ x y : Space3, ‖D x - D y‖ ≤ L * ‖x - y‖) :
    ∀ x y : Space3, ‖chi x • D x - chi y • D y‖ ≤ (c * M + C * L) * ‖x - y‖ := by
  intro x y
  -- The two nonnegativity side conditions `mul_le_mul` needs are DERIVED
  -- from the hypotheses, not assumed: each hypothesis already has an
  -- absolute value or a norm on the left, and those are nonnegative.
  have hcx : 0 ≤ c * ‖x - y‖ := le_trans (abs_nonneg _) (hchi x y)
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hchiC y)
  -- Decompose the difference so each summand is a product of a bounded
  -- scalar with a controlled difference.
  have key : chi x • D x - chi y • D y
      = (chi x - chi y) • D x + chi y • (D x - D y) := by
    simp only [sub_smul, smul_sub]
    ring
  -- `norm_add_le` is a lemma about the goal, not a rewrite rule, so it is
  -- applied in `calc` position; `norm_smul` and `Real.norm_eq_abs` turn the
  -- two scalar factors into absolute values. The vector factors carry
  -- `Space3` arguments and so are untouched by `Real.norm_eq_abs`.
  calc ‖chi x • D x - chi y • D y‖
      = ‖(chi x - chi y) • D x + chi y • (D x - D y)‖ := by rw [key]
    _ ≤ ‖(chi x - chi y) • D x‖ + ‖chi y • (D x - D y)‖ := norm_add_le _ _
    _ = |chi x - chi y| * ‖D x‖ + |chi y| * ‖D x - D y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ c * ‖x - y‖ * M + C * (L * ‖x - y‖) :=
        add_le_add
          (mul_le_mul (hchi x y) (hDM x) (norm_nonneg _) hcx)
          (mul_le_mul (hchiC y) (hD x y) (norm_nonneg _) hC)
    _ = (c * M + C * L) * ‖x - y‖ := by ring
