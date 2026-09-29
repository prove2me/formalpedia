-- Prove2me | Definitions.Def_MachineLearning_TotalVariation_DualityL1
-- name    : MachineLearning_TotalVariation_DualityL1
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:13:15.641032+00:00
-- url     : https://prove2.me/theorems/aa961348-d71c-403d-a3ab-26f97194fa0f
-- title:
--   Aether Catalog definitions — MachineLearning_TotalVariation_DualityL1
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.TotalVariation.DualityL1`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/TotalVariation/DualityL1.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_TotalVariation_EventSup
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Where the factor `1/2` comes from: `ℓ¹`–`ℓ^∞` duality of the test polytope

`EventSup` proved that the supremum of `p(A) − q(A)` over *events* is `d_TV`.
Here we prove the companion statement for **signed** tests: the supremum of
`∑ₓ (p x − q x) g x` over all `g` with `‖g‖_∞ ≤ 1` is `2 d_TV = ‖p − q‖₁`, and it
is attained at the sign pattern `g = sgn(p − q)`.

Putting the two side by side (`factor_two_dichotomy`) explains the notorious
factor of two *exactly*:

| test class            | attained supremum |
|-----------------------|-------------------|
| `g : X → [0,1]`       | `d_TV(p, q)`      |
| `g : X → [−1,1]`      | `2 d_TV(p, q)`    |

The `[0,1]` polytope is the affine image `g ↦ (1 + g)/2` of the `[−1,1]` one, and
because `∑ₓ (p x − q x) = 0` the affine shift is invisible while the factor `1/2`
survives.  The `ℓ¹` bound is therefore not merely wasteful: it is the *correct*
answer to a different, coarser question.

We also record that the sharp normalization makes `d_TV` a genuine metric
(`tvDist_triangle`, `tvDist_eq_zero_iff` from `EventSup`), with the two rigid
endpoints `0` and `1` bounding its range on the simplex — so the distinguishing
advantage is a distance, not just a divergence.

## Main results

* `signedAdvantage_le`, `exists_signedAdvantage_eq` , `isGreatest_signedAdvantage`
  — the `ℓ^∞`-dual description `‖p − q‖₁ = max_{‖g‖∞ ≤ 1} ⟨p − q, g⟩`;
* `factor_two_dichotomy` — the two suprema in one statement;
* `tvDist_triangle`, `tvDist_self` — `d_TV` is a metric on laws;
* `tvDist_affine_shift` — the invisible affine shift behind the factor two.

## Application keywords

total variation, dual norm, test polytope, linear programming duality, metric
-/


open Finset

namespace UniversalRedundancy

variable {X : Type*} [Fintype X]

/-- The advantage of a *signed* test `g : X → [−1, 1]`. -/
def signedAdvantage (p q : X → ℝ) (g : X → ℝ) : ℝ := ∑ x, (p x - q x) * g x






/-! ## `d_TV` is a metric -/



end UniversalRedundancy


