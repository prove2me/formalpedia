-- Prove2me | Definitions.Def_Bridges_TropicalCausality
-- name    : Bridges_TropicalCausality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:41:55.723046+00:00
-- url     : https://prove2.me/theorems/e788fc41-0fe8-4269-b82c-9c2491b2faa3
-- title:
--   Aether Catalog definitions — Bridges_TropicalCausality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalCausality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalCausality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Causal Ordering

This file establishes a **causal preorder** framework derived from tropical distance-like
functionals. The central insight is that any function `τ : α → α → ℝ` satisfying a
(standard additive) triangle inequality `τ x z ≤ τ x y + τ y z` induces:

1. A **budgeted causal relation** `TropicalCausal τ T x y := τ x y ≤ T`,
   with composable budgets under transitivity.
2. A **zero-budget future relation** `TropicalFuture τ x y := τ x y ≤ 0`,
   which is a preorder when `τ x x ≤ 0`.
3. **Functoriality**: tropical nonexpansive maps preserve the causal order.
4. **Concrete instantiation**: the tropical (sup) norm triangle inequality
   on `Fin n → ℝ` yields a concrete causal preorder on finite-dimensional
   tropical vector spaces.
5. **Matrix/path causality**: for min-plus weighted directed graphs,
   path-cost reachability is transitive by concatenation.

## Main definitions

- `TropicalCausal` — budgeted causal reachability
- `TropicalFuture` — zero-budget future relation
- `TropicalNonexpansive` — maps that do not increase tropical distance
- `tropicalFuturePreorder` — the induced `Preorder` instance
- `PathCost` — cost of a path in a weighted digraph
- `MatrixCausal` — path-based causal reachability in a matrix

## Main results

- `tropical_causal_transitive_budget` — budget composition under transitivity
- `tropical_future_transitive` — zero-budget transitivity
- `tropical_future_monotone_of_nonexpansive` — functoriality of causality
- `tropicalNorm_causal_transitive` — concrete instantiation via sup-norm
- `matrix_causal_transitive` — path concatenation transitivity

## References

Builds on:
- `tropical_triangle_inequality` from `Bridges/TropicalUltrametricDuality`
- `tropicalNorm_triangle` from `Tropical/RieszRepresentation/Applications`
- `tropMatMul` and `WeightedDigraph` from `Tropical/MinPlusAlgebra`
-/

open Finset

/-! ## §1. Abstract Budgeted Tropical Causality -/

/-- A point `x` can causally precede `y` under tropical displacement `τ`
with time budget `T` if the tropical displacement `τ x y ≤ T`. -/
def TropicalCausal {α : Type*} (τ : α → α → ℝ) (T : ℝ) (x y : α) : Prop :=
  τ x y ≤ T

/-- The zero-budget future relation: `y` lies in the tropical future of `x`
if the displacement `τ x y ≤ 0`. -/
def TropicalFuture {α : Type*} (τ : α → α → ℝ) (x y : α) : Prop :=
  τ x y ≤ 0





/-! ## §2. Preorder Packaging -/


/-! ## §3. Nonexpansive Maps and Functoriality -/

/-- A map `f : α → β` is **tropical nonexpansive** from `(α, τ₁)` to `(β, τ₂)` if
it does not increase displacement: `τ₂ (f x) (f y) ≤ τ₁ x y` for all `x, y`. -/
def TropicalNonexpansive {α β : Type*} (τ₁ : α → α → ℝ) (τ₂ : β → β → ℝ) (f : α → β) : Prop :=
  ∀ x y, τ₂ (f x) (f y) ≤ τ₁ x y





/-! ## §4. Budgeted Chain Composition -/

/-
**Chain composition**: a causal chain `x₀ → x₁ → ⋯ → xₙ` with individual
budgets `T₀, T₁, …, Tₙ₋₁` yields a global causal link from `x₀` to `xₙ`
with budget equal to the sum of all budgets.
-/

/-
**Future chain**: a chain of `TropicalFuture` links composes into a single
`TropicalFuture` link. Simplified version of `tropical_causal_chain` for zero budgets.
-/

/-! ## §5. Concrete Instantiation: Sup-Norm Tropical Displacement -/

/-- The **sup-norm tropical displacement** on `Fin n → ℝ`: the maximum absolute
difference of coordinates. This is a standard metric and satisfies the triangle
inequality. -/
noncomputable def tropicalSupDisplacement {n : ℕ} [NeZero n] (x y : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty) (fun i => |x i - y i|)

/-
The sup-norm displacement satisfies the triangle inequality.
-/

/-
The sup-norm displacement is reflexive (zero on the diagonal).
-/



/-! ## §6. One-Sided Tropical Causality -/

/-- **One-sided tropical displacement**: measures the maximum amount any coordinate
of `y` exceeds the corresponding coordinate of `x`. When this is ≤ 0, we have
`y ≤ x` coordinatewise, giving a nontrivial partial order. -/
noncomputable def tropicalOneSidedDisplacement {n : ℕ} [NeZero n] (x y : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => y i - x i)

/-
The one-sided displacement satisfies the triangle inequality.
-/

/-
The one-sided displacement is zero on the diagonal.
-/


/-
**Characterization**: `TropicalFuture` for the one-sided displacement is equivalent
to coordinatewise `≤`. This connects tropical causality to the natural product order.
-/

/-! ## §7. Matrix / Path Causality -/

/-- The cost of traversing a path in a weighted directed graph, defined as the
sum of edge weights along the path. An empty or singleton path has cost 0. -/
noncomputable def PathCost {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : List (Fin n) → ℝ
  | [] => 0
  | [_] => 0
  | i :: j :: rest => A i j + PathCost A (j :: rest)

/-- A path is **valid** if it is nonempty and its first and last elements match
the given source and target. -/
def ValidPath {n : ℕ} (p : List (Fin n)) (i j : Fin n) : Prop :=
  p ≠ [] ∧ p.head? = some i ∧ p.getLast? = some j

/-- **Matrix causal reachability**: vertex `i` can causally reach vertex `j` with
budget `T` if there exists a valid path from `i` to `j` with total cost ≤ `T`. -/
def MatrixCausal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (T : ℝ) (i j : Fin n) : Prop :=
  ∃ p : List (Fin n), ValidPath p i j ∧ PathCost A p ≤ T

/-
Concatenation of valid paths: if `p` is a valid path from `i` to `j` and
`q` is a valid path from `j` to `k`, then `p ++ q.tail` is a valid path from
`i` to `k`.
-/

/-
Cost of concatenated paths is bounded by the sum of individual path costs
plus the connecting edge weight.
-/

/-
**Matrix causal transitivity**: if `i` can causally reach `j` with budget `T₁`
and `j` can causally reach `k` with budget `T₂`, then `i` can causally reach `k`
with budget `T₁ + T₂`. This is the path-concatenation analogue of budgeted
causal transitivity.
-/

/-! ## §8. Bridge: Nonexpansive Maps Compose Causal Morphisms -/


/-! ## §9. Bridge: Norm-Induced Causality from Decomposition -/

/-
A tropical norm `ν` induces a displacement functional `τ x y = ν (y - x)`.
If `ν` satisfies the triangle inequality `ν (u + v) ≤ ν u + ν v` and
`ν 0 ≤ 0`, then the induced `τ` satisfies the tropical triangle inequality
and reflexivity.
-/



/-! ## §10. Security Propagation Along Causal Chains -/

/-
**Security propagation**: if `f` is tropical nonexpansive and `x` causally
precedes `y` with budget `T`, then any norm-bound security certificate at `y`
pulls back to a weakened certificate at `x`. Concretely: if `‖f y‖ ≥ λ` and
`f` is nonexpansive with respect to `τ₁, τ₂`, then the budget-adjusted bound
`‖f x‖ ≥ λ - T` holds (under the displacement metric).
-/


