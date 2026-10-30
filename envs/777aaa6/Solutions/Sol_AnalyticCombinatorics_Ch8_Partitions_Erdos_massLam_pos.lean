-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.massLam_pos
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:18:56.694429+00:00
-- url     : https://prove2.me/submissions/7e4fad3d-b371-4c78-9195-3dd60431a3e0

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_MassRateMoments
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open Filter
open scoped BigOperators Topology

noncomputable section

lemma C_pos : 0 < C := by
  dsimp [C]
  positivity

end
end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

/-!
# Mass-rate campaign: Lambert moments — definitions and the central cancellation (R8)

The critical-path brick `|kernelMass n − 1| = O(1/n)` goes through smoothed Lambert
moments `M_r(t) = Σ_m m^r σ(m) e^{−tm}` (NOT a refined pointwise summatory, which cannot
have an `o(x)` secondary at integers because of the `σ(n)` jumps).  This file banks the
definitions, the saddle parameter `λ = C/2` with `λ² = π²/6`, the Bose kernel with its
regularization, and the central algebraic cancellation of the `n^{−1/2}` coefficients:

  `−1/(2λ) + 2Z/λ³ − (C/8)·6Z/λ⁴ = 0`  (`Z = λ²`, `C = 2λ`).

Opus-authored.
-/

set_option maxHeartbeats 400000

noncomputable section

open Filter Finset
open scoped BigOperators Topology

end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
set_option maxHeartbeats 400000
open Filter Finset
open scoped BigOperators Topology
theorem solution : 0 < massLam := by
  rw [massLam]
  have := C_pos
  positivity
