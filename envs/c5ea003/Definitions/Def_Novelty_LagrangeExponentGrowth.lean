-- Prove2me | Definitions.Def_Novelty_LagrangeExponentGrowth
-- name    : Novelty_LagrangeExponentGrowth
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:31:59.182817+00:00
-- url     : https://prove2.me/theorems/9a2b4d8f-0feb-45bf-8197-8d452031df5d
-- title:
--   Aether Catalog definitions — Novelty_LagrangeExponentGrowth
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.LagrangeExponentGrowth`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/LagrangeExponentGrowth.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_LagrangeExponentCore
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

namespace LagrangeExponent

open Set Filter

/-! ## Cube–root growth -/






/-! ## Subadditivity from concavity anchored at the critical mass -/




/-! ## `σ` as an order isomorphism of the mass line -/

/-- The Lagrange exponent is an order isomorphism of `ℝ`, with inverse the critical cubic. -/
noncomputable def lagrangeExponentOrderIso : ℝ ≃o ℝ where
  toFun := lagrangeExponent
  invFun := lagrangeCubic
  left_inv := lagrangeCubic_lagrangeExponent
  right_inv := lagrangeExponent_lagrangeCubic
  map_rel_iff' := lagrangeExponent_strictMono.le_iff_le




/-! ## Equality case of the mass bridge -/




end LagrangeExponent


