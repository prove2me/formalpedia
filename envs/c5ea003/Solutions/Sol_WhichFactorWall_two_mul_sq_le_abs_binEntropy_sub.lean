-- Prove2me | solution 1 for WhichFactorWall.two_mul_sq_le_abs_binEntropy_sub
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:23:30.086436+00:00
-- url     : https://prove2.me/submissions/025bb1d6-1af0-4f21-8394-49def7777c34

-- Sol generated from Algebra/WhichFactorWallSqrtLaw.lean
import Mathlib
import Definitions.Def_Algebra_WhichFactorWallInvariant
import Theorems.Thm_WhichFactorWall_monotoneOn_binEntropy_add_sq
/-
# The which-factor wall, cycle II: the exact resolution law is a square root

`Algebra.WhichFactorWallInvariant` established that the wall (binary capacity)
determines the class imbalance *Lipschitz-stably* only away from balance, and
that **no** linear inversion constant survives as the imbalance approaches
`1/2` (`no_uniform_inversion_constant`).  That looks like bad news for the
trace battery: the mission brief concluded that "the wall carries almost no
information and should be dropped from the battery report".

This file proves that this conclusion is *wrong*, and replaces it by the exact
law.  The wall is invertible everywhere — uniformly, with no guard at all — but
with a **square-root** modulus of continuity, and the exponent `1/2` is optimal:

* `four_mul_sub_le_log_ratio` — the pointwise derivative bound
  `4 (1/2 - x) ≤ log (1-x) - log x` on `(0, 1/2]`, i.e. `binEntropy` is
  `2`-strongly concave-at-balance in the integrated sense.
* `binEntropy_diff_ge_two_mul_sq` — **Pinsker-type inverse bound**:
  `2 (q - p)² ≤ binEntropy q - binEntropy p` for `0 ≤ p ≤ q ≤ 1/2`.
  This is the sharp global replacement for the (false) linear conjecture.
* `imbalance_sqrt_stability` — **unconditional cross-population stability**:
  if two walls agree within `ε` then the imbalances agree within `√(ε/2)`.
  No guard `η`, no hypothesis beyond `p, q ∈ [0, 1/2]`.
* `binary_wall_sqrt_stability` — the same for two binary statistics on two
  different finite populations.
* `binEntropy_gap_two_sided` — the exact quadratic law at balance:
  `2 t² ≤ log 2 - binEntropy (1/2 - t) ≤ 4 t²`.
* `sqrt_law_sharp` — the exponent `1/2` cannot be improved: for every small `ε`
  there are imbalances whose walls agree within `ε` while the imbalances differ
  by `√ε / 2`.

Consequence for the battery report: a wall value is *never* uninformative; its
resolution is `Θ(ε)` away from balance and `Θ(√ε)` at balance.  A reported wall
should be published together with the resolution its error bar implies.
-/

open WhichFactorWall

open Real Set

/-! ## 1.  A derivative bound with the right behaviour at balance -/



/-! ## 2.  The Pinsker-type inverse bound -/



/-- **Pinsker-type inverse bound for the wall.**  On the balanced side the capacity
gain between two imbalances is at least twice the squared gap.  Unlike the
refuted linear bound, this holds with an absolute constant, uniformly up to
`1/2`. -/
theorem binEntropy_diff_ge_two_mul_sq {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 2⁻¹) :
    2 * (q - p) ^ 2 ≤ binEntropy q - binEntropy p := by
  have h := monotoneOn_binEntropy_add_sq ⟨hp, le_trans hpq hq⟩ ⟨le_trans hp hpq, hq⟩ hpq
  simp only at h
  nlinarith [h, sub_nonneg.2 hpq]


/-! ## 3.  Unconditional square-root stability of the wall -/



/-! ## 4.  The exact quadratic law at balance, and optimality of the exponent -/




open WhichFactorWall in
theorem solution{p q : ℝ} (hp : p ∈ Icc (0 : ℝ) 2⁻¹)
    (hq : q ∈ Icc (0 : ℝ) 2⁻¹) : 2 * (p - q) ^ 2 ≤ |binEntropy p - binEntropy q| := by
  rcases le_total p q with h | h
  · have h1 := binEntropy_diff_ge_two_mul_sq hp.1 h hq.2
    have h2 : binEntropy q - binEntropy p ≤ |binEntropy p - binEntropy q| := by
      rw [abs_sub_comm]; exact le_abs_self _
    nlinarith [h1, h2]
  · have h1 := binEntropy_diff_ge_two_mul_sq hq.1 h hp.2
    have h2 : binEntropy p - binEntropy q ≤ |binEntropy p - binEntropy q| := le_abs_self _
    nlinarith [h1, h2]
