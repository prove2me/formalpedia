-- Prove2me | solution 1 for ReweightedNPMLE.relative_error_of_exp_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:04:06.322568+00:00
-- url     : https://prove2.me/submissions/cf7f8e89-ef9e-4d1d-83ef-6c1ada6f0533

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

open ReweightedNPMLE

open scoped BigOperators
open Finset Fintype
open ReweightedNPMLE in
/-- Dividing the absolute Taylor error by an `exp (-B)` lower bound gives
the relative `2 exp(2B)` factor used in the manuscript. -/
theorem solution {a b B r : ℝ}
    (hlower : Real.exp (-B) ≤ b)
    (herror : |a - b| ≤ 2 * Real.exp B * r) :
    |a / b - 1| ≤ 2 * Real.exp (2 * B) * r := by
  have hb : 0 < b := (Real.exp_pos (-B)).trans_le hlower
  have hnonneg : 0 ≤ 2 * Real.exp B * r := (abs_nonneg (a - b)).trans herror
  rw [div_sub_one hb.ne', abs_div, abs_of_pos hb]
  calc
    |a - b| / b ≤ (2 * Real.exp B * r) / Real.exp (-B) :=
      div_le_div₀ hnonneg herror (Real.exp_pos (-B)) hlower
    _ = 2 * Real.exp (2 * B) * r := by
      rw [div_eq_mul_inv, ← Real.exp_neg]
      calc
        2 * Real.exp B * r * Real.exp (- -B) =
            2 * (Real.exp B * Real.exp (- -B)) * r := by ring
        _ = 2 * Real.exp (2 * B) * r := by
          rw [← Real.exp_add]
          congr 3 <;> ring
