-- Prove2me | Definitions.Def_ErdosProblems_Erdos1041_Counterexample_InstanceBarriers
-- name    : ErdosProblems_Erdos1041_Counterexample_InstanceBarriers
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T19:14:14.45057+00:00
-- url     : https://prove2.me/theorems/02b299e7-8b08-4293-940c-a6e793111ef8
-- title:
--   Two explicit instance barriers
-- statement:
--   Defines two real-valued functions g₁,g₂:ℂ→ℝ by rescaling the barrier functions G₁ and G₂. Their signs separate unwanted root clusters from the relevant critical component; continuity and the required zero-set and sign properties are separate theorems.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/InstanceBarriers.lean#L1-L104
--   Construction by ani: https://www.erdosproblems.com/forum/thread/1041#post-8861
--   Related paper and provenance: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L25-L99
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1662-L1772
--   AI-assisted formalization in Will Cook's project; ani is credited for the degree-seven construction. Independent correspondence of the 1958 Problem 5 wording to this modern formulation is unrecorded.

import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierAlgebra
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierGraphs
import Definitions.Def_ErdosProblems_Erdos1041_Counterexample_BarrierSigns
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
The barrier proof is placed in the child namespace `S7Proof`, alongside its
supporting algebra.  The exported theorem below is part of the successfully
checked dependency chain for `erdos1041_counterexample`.
-/
noncomputable section
namespace Erdos1041.Counterexample.S7Proof

set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

/-- Positive rescaling of the prescribed physical-coordinate graph barrier. -/
def g1 (z : ℂ) : ℝ := G1 (z / (scaleR : ℂ))
def g2 (z : ℂ) : ℝ := G2 (z / (scaleR : ℂ))













end Erdos1041.Counterexample.S7Proof

namespace Erdos1041.Counterexample



end Erdos1041.Counterexample


