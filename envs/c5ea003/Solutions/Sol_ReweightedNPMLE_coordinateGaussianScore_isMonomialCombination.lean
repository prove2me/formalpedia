-- Prove2me | solution 1 for ReweightedNPMLE.coordinateGaussianScore_isMonomialCombination
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:02:41.554246+00:00
-- url     : https://prove2.me/submissions/1a793a55-ad15-4e04-af09-6cf1128cc963

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

-- Inline helpers preserved from ReweightedNPMLE.PolynomialMoments.
section
namespace ReweightedNPMLE

open scoped BigOperators
open Finset Fintype















































theorem IsMonomialCombination.neg {d D : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : IsMonomialCombination (D := D) f) :
    IsMonomialCombination (d := d) (D := D) (fun θ => -f θ) := by
  simpa using hf.smul (-1)

theorem IsMonomialCombination.sub {d D : ℕ} {f g : (Fin d → ℝ) → ℝ}
    (hf : IsMonomialCombination (D := D) f)
    (hg : IsMonomialCombination (D := D) g) :
    IsMonomialCombination (d := d) (D := D) (fun θ => f θ - g θ) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg















@[simp]
theorem monomialEval_linear {d : ℕ} (θ : Fin d → ℝ) (i : Fin d) :
    monomialEval θ (linearCoord i) = θ i := by
  simp only [monomialEval, linearCoord, Sym.val_eq_coe]
  rw [Sym.coe_cons, Sym.coe_cons, Sym.coe_nil]
  simp [homogenizedVariable]

@[simp]
theorem monomialEval_square {d : ℕ} (θ : Fin d → ℝ) (i : Fin d) :
    monomialEval θ (squareCoord i) = (θ i) ^ 2 := by
  simp only [monomialEval, squareCoord, Sym.val_eq_coe]
  rw [Sym.coe_cons, Sym.coe_cons, Sym.coe_nil]
  simp [homogenizedVariable, pow_two]

























































end ReweightedNPMLE
end

open ReweightedNPMLE

open scoped BigOperators
open Finset Fintype
open ReweightedNPMLE in
/-- The Gaussian score is a combination of monomials of degree at most two. -/
theorem solution {d : ℕ} (x : Fin d → ℝ) :
    IsMonomialCombination (d := d) (D := 2) (coordinateGaussianScore x) := by
  have hdot :
      IsMonomialCombination (d := d) (D := 2) (coordinateDot x) := by
    simpa [coordinateDot] using
      (isMonomialCombination_reindex (d := d) (D := 2)
        x (fun i => linearCoord i))
  have hnorm :
      IsMonomialCombination (d := d) (D := 2) coordinateNormSq := by
    simpa [coordinateNormSq] using
      (isMonomialCombination_reindex (d := d) (D := 2)
        (fun _ : Fin d => (1 : ℝ)) (fun i => squareCoord i))
  change IsMonomialCombination (d := d) (D := 2)
    (fun θ => coordinateDot x θ - (1 / 2 : ℝ) * coordinateNormSq θ)
  exact hdot.sub (hnorm.smul (1 / 2))
