-- Prove2me | Definitions.Def_Applications_LagrangeRatioSpectrum_Core
-- name    : Applications_LagrangeRatioSpectrum_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:51:21.666985+00:00
-- url     : https://prove2.me/theorems/74abc8d0-8880-404b-af96-799112d775e6
-- title:
--   Aether Catalog definitions — Applications_LagrangeRatioSpectrum_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.LagrangeRatioSpectrum.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/LagrangeRatioSpectrum/Core.lean by skeleton subtraction
import Mathlib

/-!
# Lagrange constants and their behaviour under integer transformations — Core

This file sets up the basic objects behind the *ratio spectrum of Lagrange
constants under integer linear fractional transformations* studied in the
mission "Exact Ratio Spectrum of Lagrange Constants under Integer Linear
Fractional Transformations".

For a real number `x` we use the classical **approximation function**
`approx x q = q · ‖q·x‖`, where `‖·‖` is the distance to the nearest integer
(`ndist`).  The **Lagrange (approximation) constant** is
`Lc x = liminf_{q→∞} q · ‖q·x‖`, taken in `ENNReal` so that the `liminf`
machinery is unconditionally well behaved (every term is `≥ 0`).  A real number
is **badly approximable** (`Bad`) exactly when `Lc x > 0`.

The catalog target is the statement that for an integer matrix `M` with
`det M ≠ 0` the set of ratios `{ k(Mx)/k(x) }` equals `[|det M|⁻¹, |det M|]`.
This Core file proves the part of that statement living over the
**determinant `±1` affine subgroup**: `Lc` is invariant under `x ↦ ±x + b`
(`b ∈ ℤ`), so for those `M` the ratio set is exactly `{1} = [1,1]`, which is
`[|det M|⁻¹, |det M|]` since `|det M| = 1`.

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer).  The "easy" generators of `GL₂(ℤ)` acting on `x`,
namely integer translations `x ↦ x + b` and the reflection `x ↦ -x`, should
leave the Lagrange constant *exactly* invariant, because `‖q(x+b)‖ = ‖qx‖`
and `‖q(-x)‖ = ‖qx‖` hold term-by-term, not merely asymptotically.  These are
determinant `±1` transformations, so the predicted ratio is `1`, in agreement
with `[|det|⁻¹, |det|] = [1,1]`.

EXPERIMENT (Experimenter).  Proven below.  The term-by-term identities
`approx_add_intCast`, `approx_neg` reduce the `liminf` statements to a `congr`
on the underlying sequences — no real analysis is needed for the invariances.
The pointwise `ndist` facts use `round_add_intCast` and
`abs_sub_round_eq_min` / `Int.fract_neg`.

ANALYSIS (Analyst).  The invariance results are *unconditional* (they hold for
every real `x`, not only badly approximable ones) and exact.  This is the
sharpest possible behaviour and confirms the `[1,1]` prediction for the
affine `±1` family.  The genuinely hard part of the mission — *attaining every
value* of `[|det|⁻¹, |det|]` for `|det| > 1` — needs explicit constructions of
badly approximable numbers and is recorded in `FUTURE_DIRECTIONS.md`.

CRITIQUE (Critic).  None of these theorems is vacuous: they assert equalities
of `liminf`s and are used downstream (`ndist_eq_zero_iff_int` powers the
catalog bridge).  No `native_decide`, no `True`.
-/

open Filter Topology

namespace LagrangeSpectrum

/-- Distance from `y` to the nearest integer, `‖y‖`. -/
noncomputable def ndist (y : ℝ) : ℝ := |y - round y|

/-- The approximation function `q ↦ q · ‖q·x‖`, valued in `ENNReal`. -/
noncomputable def approx (x : ℝ) (q : ℕ) : ENNReal :=
  (q : ENNReal) * ENNReal.ofReal (ndist ((q : ℝ) * x))

/-- The Lagrange (approximation) constant `k(x) = liminf_{q→∞} q · ‖q·x‖`. -/
noncomputable def Lc (x : ℝ) : ENNReal := Filter.liminf (approx x) Filter.atTop


/-! ## Distance-to-nearest-integer lemmas -/





/-! ## Approximation-function identities -/




/-! ## Invariance of the Lagrange constant (determinant `±1` affine subgroup) -/




end LagrangeSpectrum


