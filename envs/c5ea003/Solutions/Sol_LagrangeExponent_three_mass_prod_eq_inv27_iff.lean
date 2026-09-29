-- Prove2me | solution 1 for LagrangeExponent.three_mass_prod_eq_inv27_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:34:57.898915+00:00
-- url     : https://prove2.me/submissions/9baf268e-4c8c-48cb-8b29-f5759592b30b

-- Sol generated from Novelty/LagrangeExponentGrowth.lean
import Mathlib
import Definitions.Def_Novelty_LagrangeExponentGrowth
/-
# Consequences of concavity: cube–root growth, subadditivity, and the AM–GM equality case

Second research cycle on the Lagrange exponent `σ t = (1 + ∛(27 t - 1)) / 3`
(`Novelty.LagrangeExponentCore`, `Novelty.LagrangeExponentConcavity`).

Having established that `σ` is (strictly) concave exactly on `[1/27, ∞)`, we now extract
the structural consequences that concavity is *for*.

## Main results

* `lagrangeExponent_le_cbrt_add_third` / `cbrt_le_lagrangeExponent` — the **cube–root
  sandwich** `∛t ≤ σ t ≤ ∛t + 1/3` on the physical range (the upper bound holds on all of
  `ℝ`).  So the growth rate is a cube root up to an additive constant `≤ 1/3`, and the
  constant is optimal: the gap is `0` at `t = 1/27` and tends to `1/3`.
* `lagrangeExponent_subadditive_shift` — concavity anchored at the critical point yields
  `σ (s + t - 1/27) + 1/3 ≤ σ s + σ t`: merging two mass distributions is *cheaper* than
  running them separately, once the critical mass is accounted for exactly once.
* `lagrangeExponent_merge_finset` — the `n`-fold merging law, by induction over a finite
  family of admissible masses: `σ (∑ mᵢ - (n-1)/27) + (n-1)/3 ≤ ∑ σ (mᵢ)`.
* `lagrangeExponentOrderIso` — `σ` is an order isomorphism of `ℝ` with inverse the critical
  cubic, hence continuous and cofinal.
* `lagrangeExponent_mass_eq_third_iff` — the **equality case** of the mass bridge: a
  three–point distribution attains the critical exponent `1/3` iff it is uniform.  This
  shows the boundary `1/27` of the concavity region is attained by exactly one
  distribution, so the guard in `lagrangeExponent_concaveOn` is tight, not slack.
-/

open LagrangeExponent

open Set Filter

/-! ## Cube–root growth -/






/-! ## Subadditivity from concavity anchored at the critical mass -/




/-! ## `σ` as an order isomorphism of the mass line -/





/-! ## Equality case of the mass bridge -/





open LagrangeExponent in
theorem solution{p q r : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (h : p + q + r = 1) : p * q * r = 1 / 27 ↔ p = 1 / 3 ∧ q = 1 / 3 ∧ r = 1 / 3 := by
  constructor
  · intro he
    have hp' : p = 1 / 3 := by
      nlinarith [sq_nonneg (p - q), sq_nonneg (q - r), sq_nonneg (p - r), sq_nonneg (3 * p - 1),
        mul_nonneg hq hr, mul_nonneg hp hq, mul_nonneg hp hr, sq_nonneg (q + r - 2 / 3)]
    have hq' : q = 1 / 3 := by
      nlinarith [sq_nonneg (p - q), sq_nonneg (q - r), sq_nonneg (p - r), sq_nonneg (3 * q - 1),
        mul_nonneg hq hr, mul_nonneg hp hq, mul_nonneg hp hr, sq_nonneg (p + r - 2 / 3)]
    exact ⟨hp', hq', by linarith⟩
  · rintro ⟨hp', hq', hr'⟩
    subst hp'; subst hq'; subst hr'; norm_num
