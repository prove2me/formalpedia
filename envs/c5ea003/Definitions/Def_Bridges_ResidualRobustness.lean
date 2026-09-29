-- Prove2me | Definitions.Def_Bridges_ResidualRobustness
-- name    : Bridges_ResidualRobustness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:37:27.275447+00:00
-- url     : https://prove2.me/theorems/5056778c-de6c-4a2f-b61b-106a01399e43
-- title:
--   Aether Catalog definitions — Bridges_ResidualRobustness
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ResidualRobustness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ResidualRobustness.lean by skeleton subtraction
import Mathlib
/-
# Certified Robustness for Multiclass Residual Score Maps

This file formalizes certified robustness theorems for multiclass residual
piecewise-linear score maps of the form `f(x) = h(x) + Σᵢ sᵢ(x)`, where
`h` is a base tropical/Hecke score map and each skip branch `sᵢ` has a
certified L∞ Lipschitz bound.

The main results convert pairwise tropical Satake separation margins for
the base classifier into robustness certificates for the full residual
architecture.
-/

open scoped BigOperators
open Finset

/-! ## Core type abbreviations -/

/-- Input vector in ℝ^d -/
abbrev Input (d : ℕ) := Fin d → ℝ

/-- Score vector: maps inputs to per-class scores -/
abbrev ScoreVec (C d : ℕ) := Input d → Fin C → ℝ

/-! ## Definitions -/

/-- Residual score map: base `h` plus sum of skip branches `s` -/
def totalScore {C d n : ℕ}
    (h : ScoreVec C d) (s : Fin n → ScoreVec C d) : ScoreVec C d :=
  fun x c => h x c + ∑ i : Fin n, s i x c

/-- Pairwise gap between class `a` and class `b` scores -/
def pairGap {C d : ℕ} (f : ScoreVec C d) (a b : Fin C) (x : Input d) : ℝ :=
  f x a - f x b

/-- Class `y` is the strict top class: all other classes score strictly lower -/
def StrictTopClass {C d : ℕ} (f : ScoreVec C d) (y : Fin C) (x : Input d) : Prop :=
  ∀ b : Fin C, b ≠ y → f x b < f x y

/-! ## Helper lemmas -/

/-
The pairwise gap is additive over addition of score vectors
-/

/-
The pairwise gap distributes over finite sums of score vectors
-/

/-
The pairwise gap of the total residual score decomposes into
    the base gap plus the sum of branch gaps
-/

/-
If each class score changes by at most `L`, the pairwise gap
    changes by at most `2 * L` (triangle inequality on differences)
-/

/-! ## Main robustness theorems -/

/-
**Residual Pairwise Robustness from Gap Budget.**
    If the total pairwise margin at center `x` exceeds the branchwise
    perturbation budget `(K₀(y,b) + Σᵢ Kᵢ(y,b)) * r`, then class `y`
    remains strictly above every competitor `b` throughout the L∞ ball.
-/

/-
**Residual Robustness from Base Gap and Skip Budget.**
    A variant where a certified lower bound `Δ(y,b,x)` for the base
    pairwise gap is provided (e.g. from tropical Satake certificates),
    separating the base and skip contributions.
-/

/-
**Uniform-Budget Robustness.**
    When using classwise uniform Lipschitz bounds (each class score
    changes by at most `Kh * r` for the base and `Ks i * r` per branch),
    the factor 2 appears from the triangle inequality on pairwise gaps.
    The margin condition `pairGap (totalScore h s) y b x > 2r(Kh + Σᵢ Ksᵢ)`
    uses the full residual score margin at the center point.

    Note: The original form `Δ y b x > 2r(...)` using only the base gap lower bound
    is valid only when skip branch gaps at x are nonnegative. This more general
    formulation uses the actual total score gap, which correctly accounts for
    potentially negative skip branch contributions at the center.
-/

/-
**Strict Top Class on Ball.**
    Combines pairwise robustness with the `StrictTopClass` predicate.
-/


