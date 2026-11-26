-- Prove2me | solution 1 for ReweightedNPMLE.coordinateGaussianTruncatedScoreExp_isMonomialCombination
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:03:19.259664+00:00
-- url     : https://prove2.me/submissions/69220c07-1cb5-44c3-b1d1-92195448d55f

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Theorems.Thm_ReweightedNPMLE_coordinateGaussianScore_isMonomialCombination

-- Inline helpers preserved from ReweightedNPMLE.PolynomialMoments.
section
namespace ReweightedNPMLE

open scoped BigOperators
open Finset Fintype





























































































/-- The `ell`th power of the Gaussian score has total degree at most `2 * ell`. -/
theorem coordinateGaussianScore_pow_isMonomialCombination
    {d : ℕ} (x : Fin d → ℝ) (ell : ℕ) :
    IsMonomialCombination (d := d) (D := 2 * ell)
      (fun θ => (coordinateGaussianScore x θ) ^ ell) := by
  induction ell with
  | zero =>
      simpa using isMonomialCombination_const (d := d) (D := 0) 1
  | succ ell ih =>
      simpa [pow_succ, Nat.mul_succ] using
        ih.mul (coordinateGaussianScore_isMonomialCombination x)































end ReweightedNPMLE
end

open ReweightedNPMLE

open scoped BigOperators
open Finset Fintype
open ReweightedNPMLE in
/--
The Gaussian score exponential truncated after order `L` is a linear
combination of monomial coordinates of total degree at most `2 * L`.
-/
theorem solution {d : ℕ}
    (L : ℕ) (x : Fin d → ℝ) :
    IsMonomialCombination (d := d) (D := 2 * L)
      (coordinateGaussianTruncatedScoreExp L x) := by
  have hterm : ∀ ell ∈ range (L + 1),
      IsMonomialCombination (d := d) (D := 2 * L)
        (fun θ => (coordinateGaussianScore x θ) ^ ell / ell.factorial) := by
    intro ell hell
    have hell_le : ell ≤ L := Nat.le_of_lt_succ (mem_range.mp hell)
    have hpadded :=
      (coordinateGaussianScore_pow_isMonomialCombination x ell).pad (2 * (L - ell))
    have hdegree : 2 * ell + 2 * (L - ell) = 2 * L := by omega
    rw [hdegree] at hpadded
    simpa [div_eq_mul_inv, mul_comm] using
      hpadded.smul ((ell.factorial : ℝ)⁻¹)
  change IsMonomialCombination (d := d) (D := 2 * L)
    (fun θ => ∑ ell ∈ range (L + 1),
      (coordinateGaussianScore x θ) ^ ell / ell.factorial)
  exact isMonomialCombination_finsetSum (range (L + 1))
    (fun ell θ => (coordinateGaussianScore x θ) ^ ell / ell.factorial) hterm
