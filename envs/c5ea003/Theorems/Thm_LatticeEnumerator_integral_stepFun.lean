-- Prove2me | Theorems.Thm_LatticeEnumerator_integral_stepFun
-- name    : LatticeEnumerator.integral_stepFun
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:52:57.081058+00:00
-- url     : https://prove2.me/theorems/d76600e5-5540-4b03-a643-e2005e1a74a8
-- title:
--   Exact identity for the weighted step integral.
-- statement:
--   **Exact identity for the weighted step integral.**
--
--   ```lean
--   theorem LatticeEnumerator.integral_stepFun{P : Set (Fin d → ℝ)} (hb : Bornology.IsBounded P) {t : ℝ} (ht : 0 < t)
--       (g : (Fin d → ℝ) → ℂ) :
--       ∫ x, (approxSet P t).indicator (fun x => g (floorMap t x)) x
--         = ((t ^ d)⁻¹ : ℝ) • weightedSum P t g := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/LatticePointFourier.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/LatticePointFourier.lean#L77

-- Thm stub generated from Cryptography/LatticePointFourier.lean
import Mathlib
import Definitions.Def_Cryptography_LatticePointEnumerator
import Definitions.Def_Cryptography_LatticePointFourier

/-!
# Recovering the Fourier transform of an indicator from lattice sums

This file develops the *weighted* form of the Gauss–Weyl counting theorem of
`Cryptography.LatticePointEnumerator`: for a bounded Jordan measurable set `P ⊆ ℝ^d` and a
bounded continuous weight `g`,

`t^{-d} · Σ_{k ∈ tP ∩ ℤ^d} g(k/t) → ∫ 1_P · g`  as `t → ∞`.

Specialising `g` to a character `x ↦ exp(-2πi⟨ξ, x⟩)` shows that the *Fourier transform of the
indicator function* of `P` is recovered, at every frequency `ξ`, as a limit of exponential sums
over the counted lattice points.  This is the analytic content of the "periodic point-counting
function whose Fourier coefficients recover the Fourier transform of the indicator function"
used in the paper.

## Main results

* `LatticeEnumerator.integral_stepFun` : the exact identity
  `∫ 1_{A_t}(x) g(⌊tx⌋/t) dx = t^{-d} Σ_{k ∈ tP ∩ ℤ^d} g(k/t)`.
* `LatticeEnumerator.tendsto_weightedSum` : the weighted counting theorem.
* `LatticeEnumerator.tendsto_fourierSum` : recovery of `∫ 1_P(x) e^{-2πi⟨ξ,x⟩} dx` from the
  lattice exponential sums.
* `LatticeEnumerator.weightedSum_one_eq_dilCount` : consistency check — for `g = 1` the weighted
  theorem specialises to `L_P(t)/t^d → vol P`.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology Complex

open LatticeEnumerator

variable {d : ℕ}

theorem LatticeEnumerator.integral_stepFun{P : Set (Fin d → ℝ)} (hb : Bornology.IsBounded P) {t : ℝ} (ht : 0 < t)
    (g : (Fin d → ℝ) → ℂ) :
    ∫ x, (approxSet P t).indicator (fun x => g (floorMap t x)) x
      = ((t ^ d)⁻¹ : ℝ) • weightedSum P t g := by sorry
