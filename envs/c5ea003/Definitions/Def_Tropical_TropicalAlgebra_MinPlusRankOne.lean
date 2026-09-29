-- Prove2me | Definitions.Def_Tropical_TropicalAlgebra_MinPlusRankOne
-- name    : Tropical_TropicalAlgebra_MinPlusRankOne
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:33:00.191743+00:00
-- url     : https://prove2.me/theorems/30eb3da1-c4d1-4fb2-9b47-73e181e09d89
-- title:
--   Aether Catalog definitions — Tropical_TropicalAlgebra_MinPlusRankOne
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.TropicalAlgebra.MinPlusRankOne`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/TropicalAlgebra/MinPlusRankOne.lean by skeleton subtraction
import Mathlib
/-
# Tropical Factor-Rank-1 Equivalence

This file establishes the foundational bridge between three characterizations of
rank-1 structure in tropical (min-plus) linear algebra:

1. **Min-plus factor rank ≤ 1**: A matrix A factors as A(i,j) = U(i,0) + V(0,j)
   through a single intermediate index.
2. **Additive separability**: A(i,j) = p(i) + q(j) for potential functions p, q.
3. **Tropical 2×2 minor vanishing**: A(i,j) + A(i',j') = A(i,j') + A(i',j) for all indices.

The equivalence of these three conditions is the first formal bridge between
tropical linear algebra, Monge-type discrete geometry, and discrete potential
theory (cohomological exactness on the complete bipartite grid).

## Main results

* `minPlusFactorRankLE_one_iff_additivelySeparable` — min-plus rank ≤ 1 ↔ additive separability
* `additivelySeparable_iff_tropicalRankOneMinorCondition` — separability ↔ 2×2 minor vanishing
* `minPlusFactorRankLE_one_iff_minorCondition` — the flagship synthesis
* `additive_separable_of_minorCondition` — basepoint reconstruction of potentials
* `additive_decomposition_unique_up_to_constant` — gauge uniqueness (up to additive constant)
* `maxPlusFactorRankLE_one_iff_minorCondition` — max-plus dual via negation

## Cross-domain significance

- **Discrete Hodge theory**: The minor condition is exactness of a 1-cocycle on the grid graph.
- **Monge arrays / optimization**: Equality in the Monge relation gives exact separability.
- **Machine learning**: Tropical rank-1 matrices model exact additive cost decompositions.
- **Mathematical physics**: The 2×2 identity is a discrete zero-curvature equation.
- **Category theory**: Separability is a tropical analogue of tensor rank 1.
-/


open Finset

/-! ## Definitions -/

/-- A matrix `A` has min-plus factor rank ≤ `k` if it can be written as
    `A(i,j) = inf_t (U(i,t) + V(t,j))` for factor matrices `U`, `V`
    with intermediate dimension `k`. For `k = 0`, `Fin 0` is empty and
    `sInf ∅ = 0` in `ℝ` (by convention), so only the zero matrix qualifies. -/
def MinPlusFactorRankLE (k : ℕ) {n m : ℕ} (A : Fin n → Fin m → ℝ) : Prop :=
  ∃ U : Fin n → Fin k → ℝ, ∃ V : Fin k → Fin m → ℝ,
    ∀ i j, A i j = sInf (Set.range (fun t : Fin k => U i t + V t j))

/-- A matrix `A` is additively separable if it factors as `A(i,j) = p(i) + q(j)`
    for potential functions `p` and `q`. This is the tropical analogue of
    (multiplicative) rank 1. -/
def AdditivelySeparable {n m : ℕ} (A : Fin n → Fin m → ℝ) : Prop :=
  ∃ p : Fin n → ℝ, ∃ q : Fin m → ℝ, ∀ i j, A i j = p i + q j

/-- The tropical 2×2 minor condition: all 2×2 "tropical minors" vanish, i.e.,
    `A(i,j) + A(i',j') = A(i,j') + A(i',j)` for all index quadruples.
    This is the vanishing of the discrete mixed second difference
    `δ²A(i,i',j,j') := A(i,j) + A(i',j') - A(i,j') - A(i',j) = 0`. -/
def TropicalRankOneMinorCondition {n m : ℕ} (A : Fin n → Fin m → ℝ) : Prop :=
  ∀ i i' j j', A i j + A i' j' = A i j' + A i' j

/-- Max-plus factor rank ≤ `k`: `A(i,j) = sup_t (U(i,t) + V(t,j))`. -/
def MaxPlusFactorRankLE (k : ℕ) {n m : ℕ} (A : Fin n → Fin m → ℝ) : Prop :=
  ∃ U : Fin n → Fin k → ℝ, ∃ V : Fin k → Fin m → ℝ,
    ∀ i j, A i j = sSup (Set.range (fun t : Fin k => U i t + V t j))

/-- The discrete mixed second difference (curvature defect). -/
def delta₂ {n m : ℕ} (A : Fin n → Fin m → ℝ) (i i' : Fin n) (j j' : Fin m) : ℝ :=
  A i j + A i' j' - A i j' - A i' j

/-! ## Helper lemmas -/







/-! ## Direction 1: Additive separability implies the minor condition -/


/-! ## Direction 2: Minor condition implies additive separability (basepoint reconstruction) -/


/-! ## The main equivalence: separability ↔ minor condition -/


/-! ## Min-plus rank ≤ 1 ↔ additive separability -/


/-! ## Flagship synthesis: min-plus rank ≤ 1 ↔ minor condition -/


/-! ## Gauge uniqueness -/


/-! ## Row-difference invariance -/


/-! ## Max-plus duality -/






/-! ## Min-plus and max-plus agree at rank 1 -/


