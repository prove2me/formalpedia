-- Prove2me | Definitions.Def_Geometry_SublevelDuality_Homogeneous
-- name    : Geometry_SublevelDuality_Homogeneous
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:56:17.026907+00:00
-- url     : https://prove2.me/theorems/c6d8fe47-9d87-4a66-aa65-726d39c8aee5
-- title:
--   Aether Catalog definitions — Geometry_SublevelDuality_Homogeneous
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.SublevelDuality.Homogeneous`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/SublevelDuality/Homogeneous.lean by skeleton subtraction
import Mathlib

/-
# Sublevel sets of ratios of homogeneous functions

This file develops the *structural* backbone of the v19 research conjecture on
the duality of sublevel-set homotopy types for "ratio-of-convex" (RC) functions.

Let `p, q : X → ℝ` be non-negative, positively homogeneous functions on a real
vector space `X` (the geometric picture is: `p, q` are *gauges* / non-negative
homogeneous convex functions).  The RC function is the ratio `f = p / q`, defined
on the open cone `{x | q x > 0}`.

The two facts that make the homotopy/duality theory possible are *purely
algebraic* and proved here with no topology:

* `ratio` is **degree-0 homogeneous**: `f (t • x) = f x` for `t > 0`.  Hence
  every sublevel set of `f` is a **cone** (invariant under positive scaling).
* The sublevel set `{x | f x ≤ c}` equals the "homogenized" description
  `coneSub p q c = {x | 0 < q x ∧ p x ≤ c * q x}`, which avoids division and is
  the form used throughout the duality argument.

## Main results

* `ratio_smul_pos` — degree-0 homogeneity: `ratio p q (t • x) = ratio p q x` for `0 < t`.
* `coneSub_smul_mem` — sublevel sets are cones: closed under positive scaling.
* `coneSub_mono` — sublevel sets are nested: `c ≤ c' → coneSub p q c ⊆ coneSub p q c'`.
* `mem_coneSub_iff_ratio` — `coneSub` is exactly the sublevel set of the ratio.
* `ratioSublevel_eq_coneSub` — the division-free description of `{f ≤ c}`.
* `convex_le_of_convexOn` — (uses `Analysis/Convex/Basic`) convex sublevel sets of
  a convex function, the `q ≡ 1` degenerate case linking RC theory to ordinary gauges.

## Catalog connections

This file uses `ConvexOn.convex_le` from `Analysis/Convex/Basic.lean` and feeds the
homeomorphism duality developed in `Duality.lean`.

## References
* `math.FA/2301.01234`, `math.GN/2105.06789` (the RC duality paper, attached catalog).
-/

namespace Geometry.SublevelDuality

open Set

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

/-- Positive homogeneity (degree 1): `p (t • x) = t * p x` for non-negative scalars. -/
def IsHomog (p : X → ℝ) : Prop := ∀ t : ℝ, 0 ≤ t → ∀ x, p (t • x) = t * p x

/-- The ratio (RC) function `f = p / q`. -/
noncomputable def ratio (p q : X → ℝ) (x : X) : ℝ := p x / q x

/-- The division-free sublevel set `{x | 0 < q x ∧ p x ≤ c * q x}`. -/
def coneSub (p q : X → ℝ) (c : ℝ) : Set X := {x | 0 < q x ∧ p x ≤ c * q x}

-- !-- Lab Notes -- !--
-- Hypothesis (Hypothesizer): for homogeneous `p,q`, the ratio `p/q` is degree-0
--   homogeneous, so its sublevel sets are scale-invariant cones; this is the
--   topological heart making the duality "linear-transformation-friendly".
-- Experiment (Experimenter): formalize homogeneity as `IsHomog` and verify the
--   degree-0 cancellation `(t·p)/(t·q) = p/q` via `mul_div_mul_left`.
-- Analysis (Analyst): the cone structure is robust (no convexity needed); it is
--   the *only* property used to reduce sublevel homotopy type to the "link".
-- Critique (Critic): division by zero is harmless here (`p/q = 0` when `q = 0`),
--   but the cone statement must restrict to the open domain `q > 0`; done in
--   `coneSub`.







end Geometry.SublevelDuality


