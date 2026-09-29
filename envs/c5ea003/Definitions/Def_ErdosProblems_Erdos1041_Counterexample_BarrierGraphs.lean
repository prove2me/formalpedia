-- Prove2me | Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
-- name    : ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T19:02:20.861173+00:00
-- url     : https://prove2.me/theorems/26ca2a5e-c634-4b4a-acfc-da6f100df6f1
-- title:
--   Explicit piecewise-linear barrier graphs
-- statement:
--   Defines the rational affine graph segments and their assembled barrier maps G₁ and G₂. The graph definitions provide concrete curves used in the separation proof; the needed sign and topological properties are proved later.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/BarrierGraphs.lean#L1-L318
--   Construction by ani: https://www.erdosproblems.com/forum/thread/1041#post-8861
--   Related paper and provenance: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L25-L99
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1662-L1772
--   AI-assisted formalization in Will Cook's project; ani is credited for the degree-seven construction. Independent correspondence of the 1958 Problem 5 wording to this modern formulation is unrecorded.

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
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

noncomputable section
namespace Erdos1041.Counterexample.S7Proof

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def l1_01 (x : ℝ) : ℝ := (955 / 3962) * x + (-31775 / 7924)
def l1_12 (x : ℝ) : ℝ := (-539296338829 / 44668564793666) * x + (4076722807313861 / 446685647936660)
def l1_23 (x : ℝ) : ℝ := (-1220013986006 / 25180573091109) * x + (47287422848540256709986673 / 5036114618221800000000000)
def l1_34 (x : ℝ) : ℝ := (-7548137935033 / 41210172423045) * x + (287305378858768 / 41210172423045)
def l2_01 (x : ℝ) : ℝ := (160740689651709 / 206050862085905) * x + (180400000748660 / 41210172417181)
def l2_12 (x : ℝ) : ℝ := (-578879533802 / 7002250177415) * x + (22984875809240463303357391 / 1400450035483000000000000)
def l2_23 (x : ℝ) : ℝ := (-167425171516501 / 215940137204435) * x + (288227186805049 / 43188027440887)

def phi1 (x : ℝ) : ℝ :=
  max (-(3 / 14 : ℝ) * x)
    (max (l1_34 x) (max (l1_23 x) (max (l1_12 x) (min (l1_01 x) ((9 / 40 : ℝ) * x)))))

def phi2 (x : ℝ) : ℝ :=
  max (-(37 / 46 : ℝ) * x)
    (max (l2_23 x) (max (l2_12 x) (max (l2_01 x) ((4 / 5 : ℝ) * x))))





def G1 (z : ℂ) : ℝ := eta z - phi1 (xi z)
def G2 (z : ℂ) : ℝ := -eta z - phi2 (xi z)















































def Hcoord (x e : ℝ) : ℝ :=
  Hpoly ((-5 * x + 4 * e) / 41) ((4 * x + 5 * e) / 41)









end Erdos1041.Counterexample.S7Proof


