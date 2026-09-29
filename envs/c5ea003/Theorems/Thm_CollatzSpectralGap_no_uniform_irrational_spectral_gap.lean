-- Prove2me | Theorems.Thm_CollatzSpectralGap_no_uniform_irrational_spectral_gap
-- name    : CollatzSpectralGap.no_uniform_irrational_spectral_gap
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:31:11.849962+00:00
-- url     : https://prove2.me/theorems/53e0b7af-d2d6-494a-89ca-ca2d3c463b43
-- title:
--   For every cutoff `N > 1` and every `C < √N`, an irrational frequency has
-- statement:
--   For every cutoff `N > 1` and every `C < √N`, an irrational frequency has
--   Collatz Fourier magnitude greater than `C`.
--
--   ```lean
--   theorem CollatzSpectralGap.no_uniform_irrational_spectral_gap    (N : ℕ) (C : ℝ) (hN : 1 < N) (hC : C < Real.sqrt N) :
--       ∃ ω : ℝ, Irrational ω ∧ C < ‖collatzFourier N ω‖ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/CollatzSpectralGap.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/CollatzSpectralGap.lean#L70

-- Thm stub generated from MachineLearning/CollatzSpectralGap.lean
import Mathlib
import Definitions.Def_MachineLearning_CollatzSpectralGap

/-!
# A Fourier obstruction to the proposed Collatz spectral gap

For a finite cutoff, the Collatz exponential sum is continuous in frequency and
has value `N` at frequency zero. Since irrational frequencies are dense, its
norm is arbitrarily close to `N` at irrational frequencies. Consequently, no
uniform bound smaller than `N`—in particular no bound smaller than `√N` when
`N > 1`—can hold at every irrational frequency.
-/

open CollatzSpectralGap

open scoped ComplexConjugate
open Filter Set

theorem CollatzSpectralGap.no_uniform_irrational_spectral_gap    (N : ℕ) (C : ℝ) (hN : 1 < N) (hC : C < Real.sqrt N) :
    ∃ ω : ℝ, Irrational ω ∧ C < ‖collatzFourier N ω‖ := by sorry
