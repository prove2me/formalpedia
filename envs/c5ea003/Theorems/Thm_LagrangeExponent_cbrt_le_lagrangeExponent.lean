-- Prove2me | Theorems.Thm_LagrangeExponent_cbrt_le_lagrangeExponent
-- name    : LagrangeExponent.cbrt_le_lagrangeExponent
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:06:08.442764+00:00
-- url     : https://prove2.me/theorems/8e97b532-e465-4a60-b74b-68fac91601f4
-- title:
--   Lower bound on the physical range: the exponent is at least the cube root.
-- statement:
--   Lower bound on the physical range: the exponent is at least the cube root.
--
--   ```lean
--   theorem LagrangeExponent.cbrt_le_lagrangeExponent{t : ℝ} (ht : 1 / 27 ≤ t) : cbrt t ≤ lagrangeExponent t := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/LagrangeExponentGrowth.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/LagrangeExponentGrowth.lean#L46

-- Thm stub generated from Novelty/LagrangeExponentGrowth.lean
import Mathlib
import Definitions.Def_Novelty_LagrangeExponentCore
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

theorem LagrangeExponent.cbrt_le_lagrangeExponent{t : ℝ} (ht : 1 / 27 ≤ t) : cbrt t ≤ lagrangeExponent t := by sorry
