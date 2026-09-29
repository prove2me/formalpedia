-- Prove2me | Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
-- name    : ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:59:19.248675+00:00
-- url     : https://prove2.me/theorems/4f0a9963-f7fe-4fe3-8349-af3e979792fd
-- title:
--   Coordinates and algebra for separating barriers
-- statement:
--   Defines the rescaled real coordinates and auxiliary polynomials used to check two separating barriers at the fixed parameter. Positivity and exclusion properties are established by separate lemmas.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/BarrierAlgebra.lean#L1-L198
--   Construction by ani: https://www.erdosproblems.com/forum/thread/1041#post-8861
--   Related paper and provenance: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L25-L99
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1662-L1772
--   AI-assisted formalization in Will Cook's project; ani is credited for the degree-seven construction. Independent correspondence of the 1958 Problem 5 wording to this modern formulation is unrecorded.

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-! External source: ani, erdosproblems.com forum thread 1041, 7 Sept 2026.
Explicit separating barriers replacing the Riemann-Hurwitz step of Lemma 2.1, at `s = 10⁻⁶`. -/

/-!
The namespace `S7Proof` keeps the barrier lemmas separate from the shared
definitions in `Defs.lean`.  These lemmas are consumed by
`InstanceBarriers.lean` and belong to the successfully checked counterexample
dependency chain.
-/
noncomputable section

open scoped ComplexConjugate

namespace Erdos1041.Counterexample.S7Proof

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def scaleR : ℝ := (ρ : ℝ) * (ε : ℝ)
def rootScale : ℝ := 1 / (ε : ℝ)
def K_hi : ℝ := 7 / 10 ^ 12 + 1 / 10 ^ 105





















def Hpoly (x y : ℝ) : ℝ :=
  1 * x ^ 7
    + (-23013813 / 32000000000000000000000000000000000000000000000000000000000000000) * x ^ 6
    + (-21) * x ^ 5 * y ^ 2
    + (243 / 6250000000000000000000000000000000000000000000000000000000000000000) * x ^ 5 * y
    + (-9 / 5000000000000000000000000000000000000000000) * x ^ 5
    + (69041439 / 6400000000000000000000000000000000000000000000000000000000000000) * x ^ 4 * y ^ 2
    + (-551827 / 160000000000000000000000000000000000000) * x ^ 4 * y
    + (329507 / 1600000000000000) * x ^ 4
    + 35 * x ^ 3 * y ^ 4
    + (-81 / 625000000000000000000000000000000000000000000000000000000000000000) * x ^ 3 * y ^ 3
    + (9 / 500000000000000000000000000000000000000000) * x ^ 3 * y ^ 2
    + (1 / 250000000000000000) * x ^ 3 * y
    + (-329507 / 1600) * x ^ 3
    + (-69041439 / 6400000000000000000000000000000000000000000000000000000000000000) * x ^ 2 * y ^ 4
    + (551827 / 80000000000000000000000000000000000000) * x ^ 2 * y ^ 3
    + (-988521 / 800000000000000) * x ^ 2 * y ^ 2
    + (3 / 1000000) * x ^ 2 * y
    + (9 / 5000000) * x ^ 2
    + (-7) * x * y ^ 6
    + (243 / 6250000000000000000000000000000000000000000000000000000000000000000) * x * y ^ 5
    + (-9 / 1000000000000000000000000000000000000000000) * x * y ^ 4
    + (-1 / 250000000000000000) * x * y ^ 3
    + (988521 / 1600) * x * y ^ 2
    + (-551827 / 400) * x * y
    + (23013813 / 32000) * x
    + (23013813 / 32000000000000000000000000000000000000000000000000000000000000000) * y ^ 6
    + (-551827 / 800000000000000000000000000000000000000) * y ^ 5
    + (329507 / 1600000000000000) * y ^ 4
    + (-1 / 1000000) * y ^ 3
    + (-9 / 5000000) * y ^ 2
    + (81 / 12500000) * y
    + (7000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001 / 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)











def xi (z : ℂ) : ℝ := -5 * z.re + 4 * z.im
def eta (z : ℂ) : ℝ := 4 * z.re + 5 * z.im






















end Erdos1041.Counterexample.S7Proof


