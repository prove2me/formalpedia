-- Prove2me | Theorems.Thm_LatticeEnumerator_shiftCount_eq_dilCount_translate
-- name    : LatticeEnumerator.shiftCount_eq_dilCount_translate
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:53:06.670278+00:00
-- url     : https://prove2.me/theorems/c07fc440-ab85-4687-a849-9144475e9ac2
-- title:
--   `shiftCount P t y` really is the lattice-point enumerator of the translate `P + y`.
-- statement:
--   `shiftCount P t y` really is the lattice-point enumerator of the translate `P + y`.
--
--   ```lean
--   theorem LatticeEnumerator.shiftCount_eq_dilCount_translate(P : Set (Fin d → ℝ)) (t : ℝ) (y : Fin d → ℝ) :
--       shiftCount P t y = dilCount ((fun x => x + y) '' P) t := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/LatticePointUniqueness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/LatticePointUniqueness.lean#L67

-- Thm stub generated from Cryptography/LatticePointUniqueness.lean
import Mathlib
import Definitions.Def_Cryptography_LatticePointEnumerator
import Definitions.Def_Cryptography_LatticePointUniqueness

/-!
# A uniqueness theorem for lattice-point enumerators of integer translates

Let `P ⊆ ℝ^d` be bounded and let

`L_{P+v}(t) = |t(P+v) ∩ ℤ^d|`,  `t > 0` real, `v ∈ ℤ^d`,

be the family of real-parameter lattice-point enumerators of all *integer* translates of `P`
(`LatticeEnumerator.shiftCount P t v`).  The main theorem of the paper
*A Fourier-analytic uniqueness theorem for lattice-point enumerators* states that this data
determines the indicator function of `P` almost everywhere, provided `P` is bounded,
measurable and has null topological frontier.

This file gives a complete, **elementary** proof of that statement (and of a strictly stronger
pointwise statement), avoiding Fourier analysis altogether.

## The mechanism

Fix a rational point `x = a/N ∈ ℚ^d` and put

`M = ⌈2R⌉ + 2`,  `q = N·M + 1`,  `t = N/q`,  `v = M·a ∈ ℤ^d`,

where `P ∪ Q ⊆ closedBall 0 R`.  The counted grid `(1/t)ℤ^d - v = (q/N)ℤ^d - M a` has spacing
`q/N = M + 1/N > 2R`, hence **at most one** of its points can lie in the ball of radius `R`;
and the lattice point `k = a` produces exactly the probe point

`a/t - v = a(M + 1/N) - M a = a/N = x`.

Consequently `L_{P+v}(t) = 1` if `x ∈ P` and `= 0` otherwise: the enumerator data *reads off*
the indicator of `P` at every rational point (`mem_iff_mem_of_integerTranslateData`).
Since `ℚ^d` is dense and, off the (null) frontier, membership is a local property, the
indicators agree almost everywhere.

## Main results

* `LatticeEnumerator.shiftCount_eq_one`, `LatticeEnumerator.shiftCount_eq_zero` : the
  sparse-grid evaluation lemmas.
* `LatticeEnumerator.mem_iff_mem_of_gridRepresentation` : the master lemma — membership is
  determined at every point of the form `s·k - v` with `k, v ∈ ℤ^d` and `s` large.
* `LatticeEnumerator.mem_iff_mem_of_integerTranslateData` : the data determines membership at
  every rational point — *exactly*, with no regularity hypothesis whatsoever.
* `LatticeEnumerator.ae_eq_of_integerTranslateData` : the paper's theorem, `P =ᵐ Q`, for
  bounded sets with null frontier.
* `LatticeEnumerator.volume_symmDiff_eq_zero_of_integerTranslateData` : the same, stated as
  `vol(P Δ Q) = 0`.
* `LatticeEnumerator.convexBody_eq_of_integerTranslateData` : the corollary for convex bodies:
  interiors and closures coincide.
* `LatticeEnumerator.eq_of_integerTranslateData_dim_one` : in dimension one the conclusion
  upgrades to exact set equality, with no measurability or frontier hypothesis.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology

open LatticeEnumerator

variable {d : ℕ}

theorem LatticeEnumerator.shiftCount_eq_dilCount_translate(P : Set (Fin d → ℝ)) (t : ℝ) (y : Fin d → ℝ) :
    shiftCount P t y = dilCount ((fun x => x + y) '' P) t := by sorry
