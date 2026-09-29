-- Prove2me | Definitions.Def_ErdosProblems_Erdos269_PaperR7AnalyticInterfaces
-- name    : ErdosProblems_Erdos269_PaperR7AnalyticInterfaces
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:12:43.10751+00:00
-- url     : https://prove2.me/theorems/5ee84ccc-a1a3-48dd-927e-0f84b2a07ed6
-- title:
--   PaperR7AnalyticInterfaces
-- statement:
--   Defines a two-prime Hecke-type series value, rational polynomials for distinct and repeated value reductions, and the real carry matrix. The named analytic transcendence input is a separate hypothesis, not supplied by these definitions.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperR7AnalyticInterfaces.lean#L1-L108
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Shared_IrrationalRotationStaircase
import Definitions.Def_ErdosProblems_Erdos269_KernelCarryRank
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Real.Archimedean
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Round 7: proved algebra around explicitly unresolved analytic inputs

This file DOES NOT prove the two-prime transcendence theorem. Its final algebraic
step is separated from THREE hypotheses still requiring analytic proofs:
transcendence of the specified Hecke--Mahler value, and the two identities for
the actual series. The parameters are visible, not axioms or admitted theorems.

It also proves the constant rank-one upper witness for the uniform carry
approximation. The lower bound over every finite separated rank remains open
as a formalisation obligation in this return.

Validation: authored, not compiled. No admissions.
-/

namespace ErdosProblems.Erdos269.PaperR7

open Polynomial

/-- Exact value named `A` on the page; this definition makes no arithmetic assertion. -/
noncomputable def twoPrimeHeckeValue (p q : ℕ) : ℝ :=
  ∑' n : ℕ, ((p : ℝ)⁻¹) ^ n *
    ((q : ℝ)⁻¹) ^ ⌊(n : ℝ) * Real.logb q p⌋₊



noncomputable def distinctValuePolynomial (p q : ℚ) : ℚ[X] :=
  C ((q - p) / (q - 1)) * X + C (p / (q - 1))

noncomputable def repeatedValuePolynomial (p q : ℚ) : ℚ[X] :=
  C ((p + q - 1) / (q - 1)) * X - C ((p - 1) / (q - 1)) * X ^ 2



/-- The normalised real-valued carry matrix, using the actual integer-log carry. -/
noncomputable def realCarryMatrix (p q r i j : ℕ) : ℝ :=
  ((r : ℝ)⁻¹) ^ logCarry r (p ^ i) (q ^ j)



end ErdosProblems.Erdos269.PaperR7


