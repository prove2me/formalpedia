-- Prove2me | solution 1 for LagrangeExponent.cbrt_le_lagrangeExponent
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:30:51.075134+00:00
-- url     : https://prove2.me/submissions/6e5a8849-dfd3-459d-9c05-442b0ffc603f

-- Sol generated from Novelty/LagrangeExponentGrowth.lean
import Mathlib
import Definitions.Def_Novelty_LagrangeExponentCore
import Definitions.Def_Novelty_LagrangeExponentGrowth
import Theorems.Thm_LagrangeExponent_cbrt_zero
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
theorem solution{t : ℝ} (ht : 1 / 27 ≤ t) : cbrt t ≤ lagrangeExponent t := by
  set A := cbrt (27 * t - 1) with hA
  have hA0 : 0 ≤ A := by
    have : cbrt 0 ≤ cbrt (27 * t - 1) := cbrt_strictMono.monotone (by linarith)
    simpa [hA] using this
  have hcube : (A + 1) ^ 3 = 27 * t + (3 * A ^ 2 + 3 * A) := by
    have h3 : A ^ 3 = 27 * t - 1 := by rw [hA, cbrt_cube]
    nlinarith [h3]
  have hge : (3 * cbrt t) ^ 3 ≤ (A + 1) ^ 3 := by
    have hct : (cbrt t) ^ 3 = t := cbrt_cube t
    nlinarith [hcube, sq_nonneg A, hA0, hct]
  have : 3 * cbrt t ≤ A + 1 := by
    by_contra hcon
    push_neg at hcon
    have := cube_strictMono hcon
    simp only at this
    linarith
  unfold lagrangeExponent
  linarith
