-- Prove2me | Definitions.Def_Bridges_TropicalEcosystemDynamics
-- name    : Bridges_TropicalEcosystemDynamics
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:42:08.451371+00:00
-- url     : https://prove2.me/theorems/5282c2c8-e3fc-4c64-97f9-89d01c4c6557
-- title:
--   Aether Catalog definitions — Bridges_TropicalEcosystemDynamics
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalEcosystemDynamics`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalEcosystemDynamics.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Ecosystem Dynamics: Predator-Prey as Min-Plus Lotka-Volterra

This file establishes a rigorous formalization of predator-prey dynamics in the
framework of min-plus (tropical) algebra. The central object is a discrete
update operator `TropPredPrey` on `ℝ × ℝ` defined by:

- prey update:   `x_{n+1} = min (a + x_n) (b + y_n)`
- predator update: `y_{n+1} = min (c + x_n) (d + y_n)`

for real parameters `a b c d`. This is the min-plus analogue of a linear
interaction system, and its dynamics encode ecological trajectories.

## Main results

* `trop_pred_prey_fixed_point_invariant`: Fixed points of `TropPredPrey` are
  preserved under all iterates. This is the ecological anchor: equilibria persist.

* `trop_eigenvalue_2x2_is_min_cycle_mean`: The tropical eigenvalue
  `μ = min a (min d ((b+c)/2))` equals the minimum cycle mean of the associated
  2-node weighted digraph.

* `trop_eigenvector_iterates`: If `v` is a tropical eigenvector with eigenvalue `μ`,
  then `F^[n] v = (n*μ + v.1, n*μ + v.2)`. This identifies the ecological
  "canonical period" as a tropical linear drift rate.

* `trop_pred_prey_nonexpansive`: The map `TropPredPrey` is nonexpansive in the
  sup-norm (L∞ metric). This provides stability without spectral radius assumptions.

* `trop_translate_commute`: Translation by `μ` commutes with `TropPredPrey` in the
  eigenvector sense, establishing tropical linearity.

## References

This formalization connects to the catalog theorems:
- `tropical_plus_distributes_over_min` from `MinPlusVerificationCore`
- `fixed_points_are_iterative_invariants` from `ClosureRenormalizationDuality`
- `tropical_spectral_stability` from `BreakthroughDirections`

## Tags

tropical algebra, min-plus, predator-prey, Lotka-Volterra, nonexpansive map,
tropical eigenvalue, cycle mean, ecological dynamics
-/

open Function

noncomputable section

/-! ## Core Definitions -/

/-- The tropical predator-prey update map on `ℝ × ℝ`.
    Given interaction parameters `a b c d`, this defines:
    - prey update:   `x' = min(a + x, b + y)`
    - predator update: `y' = min(c + x, d + y)` -/
def TropPredPrey (a b c d : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  fun p => (min (a + p.1) (b + p.2), min (c + p.1) (d + p.2))

/-- The two-cycle mean of the predator-prey interaction:
    the average weight of the cycle prey → predator → prey. -/
def twoCycleMean (b c : ℝ) : ℝ := (b + c) / 2

/-- The tropical eigenvalue for a 2×2 min-plus system.
    This is the minimum cycle mean over all simple cycles:
    - self-loop at prey: `a`
    - self-loop at predator: `d`
    - 2-cycle prey↔predator: `(b+c)/2` -/
def tropEigenValue2 (a b c d : ℝ) : ℝ :=
  min a (min d ((b + c) / 2))


/-- The sup-norm (L∞) distance between two points in `ℝ × ℝ`. -/
def supDist (p q : ℝ × ℝ) : ℝ :=
  max (|p.1 - q.1|) (|p.2 - q.2|)

/-! ## Theorem 1: Fixed points are iteratively invariant -/

/-
**Ecological equilibria are tropical fixed points.**
    If `p` is a fixed point of `TropPredPrey a b c d`, then all iterates
    preserve `p`. This is the certified anchor for ecological dynamics:
    once an equilibrium is reached, the system remains there forever.

    This is the concrete instantiation of the abstract catalog theorem
    `fixed_points_are_iterative_invariants` for the predator-prey setting.
-/

/-! ## Theorem 2: Tropical eigenvalue is minimum cycle mean -/

/-
**Tropical eigenvalue formula for the 2-species interaction matrix.**
    The tropical eigenvalue equals the minimum cycle mean of the 2-node
    weighted digraph with:
    - self-loop weight `a` at prey node
    - self-loop weight `d` at predator node
    - 2-cycle mean `(b+c)/2` for the prey↔predator cycle
-/

/-! ## Key Lemma: Tropical translation commutes with TropPredPrey -/

/-
**Tropical translation commutes with the update map.**
    If `F(v) = (μ + v.1, μ + v.2)`, then `F(μ + v.1, μ + v.2) = (2μ + v.1, 2μ + v.2)`.
    More generally, adding `μ` to both coordinates of the input adds `μ` to both
    coordinates of the output. This is the key step in the eigenvector iteration proof,
    powered by tropical distributivity: `r + min u v = min (r + u) (r + v)`.
-/

/-! ## Theorem 3: Eigenvector iterates grow linearly -/

/-
**Canonical period/growth rate is determined by the tropical eigenvalue.**
    If `v` is a tropical eigenvector with eigenvalue `μ`, then the `n`-th iterate
    satisfies `F^[n](v) = (n*μ + v.1, n*μ + v.2)`. This identifies the ecological
    "canonical period" as a tropical linear drift rate.

    The proof proceeds by induction, using `trop_translate_commute` and
    `tropical_plus_distributes_over_min` for the inductive step.
-/

/-! ## Theorem 4: Nonexpansiveness in sup-norm -/

/-
**Auxiliary: min is nonexpansive in sup-norm.**
    `|min(a₁+x₁, b₁+y₁) - min(a₂+x₂, b₂+y₂)| ≤ max(|x₁-x₂|, |y₁-y₂|)`
    when the additive constants are the same.
-/

/-
**The tropical predator-prey map is nonexpansive in sup-norm.**
    For any two points `p, q ∈ ℝ × ℝ`:
    `supDist (F p) (F q) ≤ supDist p q`

    This is a fundamental stability result: the map never increases distances.
    It follows from the elementary fact that `min` is nonexpansive, combined
    with the observation that additive translation preserves distances.

    This nonexpansiveness is compositional and certifiable, providing stronger
    guarantees than spectral radius conditions alone.
-/

/-! ## Bridge to catalog: Tropical spectral stability -/

/-
**Bridge theorem connecting concrete eigenvalue to abstract spectral stability.**
    When the tropical eigenvalue satisfies `0 ≤ μ ≤ 1`, the eigenmode
    exhibits bounded polynomial growth: `μ^n ≤ 1` for all `n`.

    This bridges the concrete `tropEigenValue2` to the abstract catalog theorem
    `tropical_spectral_stability` from `BreakthroughDirections`.
-/

/-
**Eigenvector growth is bounded when eigenvalue is in [0,1].**
    If the tropical eigenvalue `μ` satisfies `0 ≤ μ ≤ 1` and `v` is an
    eigenvector, then the iterates grow at most linearly with slope 1.
-/

/-! ## Monotonicity of TropPredPrey -/

/-
**TropPredPrey is coordinatewise monotone.**
    If `p.1 ≤ q.1` and `p.2 ≤ q.2`, then `(F p).1 ≤ (F q).1` and `(F p).2 ≤ (F q).2`.
    This shows the ecological dynamics preserve the natural partial order.
-/

end


