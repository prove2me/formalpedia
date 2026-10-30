-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.massLam_sq
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T16:54:54.887904+00:00
-- url     : https://prove2.me/submissions/4e9dc704-29f6-4502-b0a8-88af255fe650

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

lemma C_sq_eq_four_mul_A : C ^ 2 = 4 * Partitions.A := by
  dsimp [C, Partitions.A]
  rw [mul_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 / 3 : ℝ))]
  ring

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
theorem solution : massLam ^ 2 = Real.pi ^ 2 / 6 := by
  rw [massLam, div_pow]
  have h := C_sq_eq_four_mul_A
  have hA : Partitions.A = Real.pi ^ 2 / 6 := rfl
  rw [h, hA]
  ring
