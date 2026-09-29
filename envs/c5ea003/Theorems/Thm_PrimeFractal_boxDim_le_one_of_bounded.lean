-- Prove2me | Theorems.Thm_PrimeFractal_boxDim_le_one_of_bounded
-- name    : PrimeFractal.boxDim_le_one_of_bounded
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:30:55.033712+00:00
-- url     : https://prove2.me/theorems/cfa57ca3-85de-4a70-8db9-6da5cdc778e6
-- title:
--   The universal ceiling.
-- statement:
--   **The universal ceiling.** Every bounded subset of `ℝ` has upper box dimension `≤ 1`:
--   for each `ε > 0`, eventually `log (boxCountSet S m) / log m ≤ 1 + ε`.
--
--   ```lean
--   theorem PrimeFractal.boxDim_le_one_of_bounded{S : Set ℝ} {c : ℝ} (hc : 0 < c) (hS : S ⊆ Set.Icc 0 c)
--       {ε : ℝ} (hε : 0 < ε) :
--       ∀ᶠ m : ℕ in atTop, Real.log (boxCountSet S m) / Real.log m ≤ 1 + ε := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/PrimeFractalRefined.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/PrimeFractalRefined.lean#L69

-- Thm stub generated from NumberTheory/PrimeFractalRefined.lean
import Mathlib
import Definitions.Def_NumberTheory_PrimeFractalBoxDimension
import Definitions.Def_NumberTheory_PrimeFractalRefined

/-!
# Refined box-counting: a universal ceiling and a logarithmic defect

Two refinements of `NumberTheory.PrimeFractalBoxDimension`.

## 1. A universal ceiling: no subset of `ℝ` can have box dimension `> 1`

`boxCountSet S m` counts the boxes of size `1/m` meeting a set `S ⊆ ℝ`.  For any
`S` contained in a bounded interval, `boxCountSet_le` gives
`boxCountSet S m ≤ ⌊c m⌋ + 1`, whence `boxDim_le_one_of_bounded`:

  for every `ε > 0`, eventually `log (boxCountSet S m) / log m ≤ 1 + ε`.

This settles the mission's `1 + ε` conjecture *structurally*: whatever the
twin primes do, a subset of the line has box dimension at most `1`.  The value
`ε = 0` is not an accident of the primes; it is forced by the ambient
dimension.  (The Hausdorff dimension is likewise `≤ 1`, and for the primes it
is in fact `0`.)

## 2. A logarithmic defect: `boxCount m = Θ(m / log m)`, not `Θ(m)`

Chebyshev's *upper* bound (from Mathlib) plus a splitting of the primes at `m`
gives `eventually_boxCount_le`: `boxCount m ≤ 5 m / log m`.  Hence
`tendsto_boxCount_div_self`: `boxCount m / m → 0`.  So although the box
dimension is exactly `1`, the prime fractal has *zero one-dimensional Minkowski
content*: it is a dimension-`1` set that occupies a vanishing fraction of the
boxes a genuine interval would occupy.  This is the precise sense in which the
primes "fill out a line" — only up to a logarithmic factor, and they carry no
length at all.
-/

open PrimeFractal

open Filter Topology

/-! ### 1. The universal ceiling -/

theorem PrimeFractal.boxDim_le_one_of_bounded{S : Set ℝ} {c : ℝ} (hc : 0 < c) (hS : S ⊆ Set.Icc 0 c)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, Real.log (boxCountSet S m) / Real.log m ≤ 1 + ε := by sorry
