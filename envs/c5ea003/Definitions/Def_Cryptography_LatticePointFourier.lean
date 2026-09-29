-- Prove2me | Definitions.Def_Cryptography_LatticePointFourier
-- name    : Cryptography_LatticePointFourier
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:19:41.783238+00:00
-- url     : https://prove2.me/theorems/ed90378d-74c9-4654-80a1-51260663c81f
-- title:
--   Aether Catalog definitions — Cryptography_LatticePointFourier
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.LatticePointFourier`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/LatticePointFourier.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_LatticePointEnumerator

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

namespace LatticeEnumerator

variable {d : ℕ}

/-- The lattice sum `Σ_{k ∈ tP ∩ ℤ^d} g(k/t)` of a weight `g` over the counted lattice
points. -/
def weightedSum (P : Set (Fin d → ℝ)) (t : ℝ) (g : (Fin d → ℝ) → ℂ) : ℂ :=
  ∑ᶠ k ∈ dilLattice P t, g (fun i => (k i : ℝ) / t)






/-- The character `x ↦ exp(-2πi⟨ξ, x⟩)` on `ℝ^d`. -/
def latticeChar (ξ : Fin d → ℝ) (x : Fin d → ℝ) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) * (∑ i, ξ i * x i : ℝ))





end LatticeEnumerator


