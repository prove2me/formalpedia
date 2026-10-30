-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ModelAssembly
-- name    : AnalyticCombinatorics_Ch8_Partitions_ModelAssembly
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-28T13:30:19.632912+00:00
-- url     : https://prove2.me/theorems/e086e653-2436-493e-b4a2-97908241398e
-- title:
--   Model Assembly mathematical objects
-- statement:
--   For reals $C,a,b$, `modelIntegral C a b` is the interval integral $\int_a^b \frac{\pi^2}{6}\,y\,e^{-(C/2)y}\,dy$.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/ModelAssembly.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Mesh assembly for the model-kernel window limit

This file assembles the banked block squeeze and half-open mass limit over a uniform
arithmetic mesh: the half-open block `(a√n, b√n]` partitions into `N` mesh blocks, each
block is squeezed by endpoint exponentials times its half-open mass, and as `n → ∞` the
mesh sums converge to the Stieltjes endpoint sums `lowerMesh`/`upperMesh`.

Main result: `blockSum_eventually_between_mesh_eps` — for any fixed mesh and `ε > 0`,
eventually `lowerMesh − ε ≤ blockSum n ≤ upperMesh + ε`.

The remaining real-variable step (mesh sums → ∫ a..b (π²/6) y e^{−(C/2)y} dy as the mesh
refines) is the next brick; combining the two yields the model-kernel window limit.
ChatGPT-draft + Opus-fix.
-/

set_option maxHeartbeats 400000

noncomputable section

open Filter Finset
open scoped BigOperators Topology Interval

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos.Model

local notation "σR" => Sigma.sigmaR

/-- The target interval integral. -/
noncomputable def modelIntegral (C a b : ℝ) : ℝ :=
  ∫ y in a..b, (Real.pi ^ 2 / 6) * y * Real.exp (-(C / 2) * y)

end AnalyticCombinatorics.Ch8.Partitions.Erdos.Model


