-- Prove2me | Definitions.Def_Applications_DelaunayContraction_Inhomogeneous
-- name    : Applications_DelaunayContraction_Inhomogeneous
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:41:43.289012+00:00
-- url     : https://prove2.me/theorems/3c4bee2a-b374-4460-a747-7d25d626412c
-- title:
--   Aether Catalog definitions — Applications_DelaunayContraction_Inhomogeneous
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.DelaunayContraction.Inhomogeneous`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/DelaunayContraction/Inhomogeneous.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

/-!
# Inhomogeneous minicenter Delaunay refinement with additive contraction defect

This file develops the theory of an *inhomogeneous* contraction recurrence

  `d (k+1) ≤ a · d k + b`,   with `0 ≤ a < 1` and `b ≥ 0`,

the natural generalization of the homogeneous Delaunay contraction theory in
`Contraction.lean` (`d (k+1) ≤ (1/λ) · d k`). Geometrically, `d k` models the
maximum simplex diameter after `k` rounds of minicenter refinement, the factor
`a` is the per-step contraction of the geometry, and the *additive defect* `b`
models a persistent bounded perturbation introduced at every step by the
insertion of fresh Steiner points (each insertion can enlarge a local
neighbourhood by at most `b`).

## Main results

* `d_le_closedForm` : the exact closed-form upper bound
  `d k ≤ a^k · d 0 + b · (1 - a^k) / (1 - a)`, proved by induction.
* `excess_le_pow` : the transient `d k - L` decays geometrically,
  `d k - L ≤ a^k · (d 0 - L)`, where `L = b/(1-a)` is the steady state.
* `closedFormBound_tendsto` / `eventually_lt_fixedPoint_add` : the closed-form
  bound converges to `L = b/(1-a)`, so the iterates are eventually trapped in the
  band `[0, L + ε]`.
* `tendsto_of_exact`, `dist_le_pow_of_exact` : **genuine** convergence to
  `b/(1-a)` and a two-sided geometric decay rate hold under the *exact*
  recurrence `d (k+1) = a · d k + b`. (With only the inequality this can fail,
  e.g. `d ≡ 0` when `b > 0`, so the equality hypothesis is essential.)
* `d_le_uniform`, `perturbation_le` : the "bounded neighbourhood perturbation"
  picture — every iterate stays in `[0, d 0 + L]` and each step perturbs by `≤ b`.
* `affine_isFixedPt`, `fixedPoint_unique`, `affine_dist` : the fixed-point
  theory connection. The update map `x ↦ a·x + b` is a contraction with unique
  fixed point `b/(1-a)`.
* `affineIteration` : a concrete process realizing the exact recurrence, showing
  the bounds are tight.
-/

namespace DelaunayContraction.Inhomogeneous

open Filter Topology

/-- An *inhomogeneous contraction process*: a nonnegative real sequence (think:
maximum simplex diameter after `k` minicenter refinements) that contracts by a
uniform factor `0 ≤ a < 1` each step, up to a persistent additive defect `b ≥ 0`
(the bounded perturbation introduced by Steiner-point insertion). -/
structure InhomogeneousContractionProcess where
  /-- The quantity being contracted (e.g. maximum simplex diameter at step `k`). -/
  d : ℕ → ℝ
  /-- The (multiplicative) contraction factor. -/
  a : ℝ
  /-- The additive contraction defect (steady-state perturbation strength). -/
  b : ℝ
  a_nonneg : 0 ≤ a
  a_lt_one : a < 1
  b_nonneg : 0 ≤ b
  d_nonneg : ∀ k, 0 ≤ d k
  contracts : ∀ k, d (k + 1) ≤ a * d k + b

namespace InhomogeneousContractionProcess

variable (P : InhomogeneousContractionProcess)

/-
The denominator `1 - a` is positive.
-/

/-- The steady state / fixed point `L = b / (1 - a)`. -/
noncomputable def fixedPoint : ℝ := P.b / (1 - P.a)

/-
The steady state is nonnegative.
-/

/-
The defining identity of the fixed point: `a · L + b = L`.
-/

/-! ### Component 1: the exact closed-form bound (by induction) -/

/-
**Closed-form bound.** After `k` refinements,
`d k ≤ a^k · d 0 + b · (1 - a^k) / (1 - a)`.
Proved by induction: the base case `k = 0` is an equality, and the inductive step
combines `contracts` with the inductive hypothesis via the algebraic identity
`a · b(1-a^n)/(1-a) + b = b(1-a^{n+1})/(1-a)`.
-/

/-
The closed-form bound rewritten around the fixed point `L`:
`a^k · d 0 + b(1-a^k)/(1-a) = a^k · (d 0 - L) + L`.
-/

/-
**Geometric decay of the transient.** The excess over the steady state decays
at least geometrically: `d k - L ≤ a^k · (d 0 - L)`.
-/

/-! ### Component 2: convergence to the steady state `b/(1-a)` -/

/-
The closed-form bound converges to the fixed point `L = b/(1-a)`.
-/

/-
**One-sided convergence (general inequality case).** For any tolerance
`ε > 0`, eventually every iterate lies below `L + ε`. (Only the upper side holds
in general: the inequality `d (k+1) ≤ a d k + b` does not force convergence — e.g.
`d ≡ 0` satisfies it when `b > 0` — so we cannot claim genuine convergence here.)
-/

/-
**Iteration-count bound.** For any tolerance there is a finite number of steps
after which the iterate stays below `L + ε`.
-/

/-! ### Component 3: exponential decay under the exact recurrence

With only the inequality, genuine (two-sided) convergence can fail. Under the
*exact* recurrence `d (k+1) = a · d k + b` everything is sharp. -/

/-
Under the exact recurrence, the excess is *exactly* `a^k · (d 0 - L)`.
-/

/-
**Genuine convergence.** Under the exact recurrence the sequence converges to
the steady state `b/(1-a)`.
-/

/-
**Exponential decay rate.** Under the exact recurrence the distance to the
steady state decays exactly geometrically: `|d k - L| = a^k · |d 0 - L|`. In
particular convergence is exponential whenever `a > 0` and `d 0 ≠ L`.
-/

/-! ### Component 4: bounded neighbourhood perturbation (geometric intuition) -/

/-
Each refinement step perturbs the quantity by at most the defect `b` beyond
pure contraction: `d (k+1) - a · d k ≤ b`. This is the formal content of
"persistent Steiner insertion introduces a bounded neighbourhood perturbation".
-/

/-
**Uniform band.** Every iterate stays within the bounded neighbourhood
`[0, d 0 + L]`: contraction plus a bounded persistent perturbation keeps the
whole trajectory bounded.
-/

/-! ### Component 5: connection to fixed-point theorems -/


/-
**Uniqueness of the fixed point.** Any fixed point of `x ↦ a · x + b` equals
`b/(1-a)`.
-/

/-
The update map `x ↦ a · x + b` is a contraction with ratio `a`:
`dist (a x + b) (a y + b) = a · dist x y`. This is the metric-space fixed-point
mechanism underlying the convergence (Banach fixed-point theorem on `ℝ`).
-/

end InhomogeneousContractionProcess

/-! ### A concrete realization: the affine iteration

The exact recurrence is realized by `d k = a^k · (D - L) + L` for any starting
value `D ≥ L`, exhibiting tightness of all the bounds above. -/

/-- The exact affine iteration started at `D ≥ b/(1-a)`. Its trajectory is
`d k = a^k · (D - b/(1-a)) + b/(1-a)`, converging to `b/(1-a)`. -/
noncomputable def affineIteration (a b D : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hb : 0 ≤ b) (hD : b / (1 - a) ≤ D) : InhomogeneousContractionProcess where
  d k := a ^ k * (D - b / (1 - a)) + b / (1 - a)
  a := a
  b := b
  a_nonneg := ha0
  a_lt_one := ha1
  b_nonneg := hb
  d_nonneg := fun k => by
    have hpos : (0 : ℝ) < 1 - a := by linarith
    have h1 : (0 : ℝ) ≤ a ^ k := pow_nonneg ha0 k
    have h2 : (0 : ℝ) ≤ D - b / (1 - a) := by linarith
    have h3 : (0 : ℝ) ≤ b / (1 - a) := div_nonneg hb hpos.le
    nlinarith [mul_nonneg h1 h2]
  contracts := fun k => by
    have hpos : (0 : ℝ) < 1 - a := by linarith
    have hne : (1 - a) ≠ 0 := ne_of_gt hpos
    have key : a * (b / (1 - a)) + b = b / (1 - a) := by field_simp; ring
    have hid : a * (a ^ k * (D - b / (1 - a)) + b / (1 - a)) + b
        - (a ^ (k + 1) * (D - b / (1 - a)) + b / (1 - a))
        = a * (b / (1 - a)) + b - b / (1 - a) := by rw [pow_succ]; ring
    linarith [key, hid]


end DelaunayContraction.Inhomogeneous


