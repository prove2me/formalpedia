-- Prove2me | Definitions.Def_Nonadditivity_QuantumHolevo
-- name    : Nonadditivity_QuantumHolevo
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:33:36.221599+00:00
-- url     : https://prove2.me/theorems/be2cd98f-8b3a-49a8-9193-ea341cceee4f
-- title:
--   Holevo information of actual channel output ensembles
-- statement:
--   For a finite Kraus channel, the output set consists of the density matrices obtained from all input density matrices. Its single-use Holevo information is the supremum of the information of all normalized finite ensembles in that output set; its minimum output entropy is the corresponding infimum of entropy. A uniform lower bound on output entropy gives a Holevo upper bound. The interface also transfers an adjoint norm certificate to output purity and entropy estimates, using natural logarithms.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/QuantumHolevo.lean#L27-L67

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_StateEnsembles
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/





/-! # Holevo information of concrete Kraus channels

The quantity below is defined by all finite ensembles of actual channel
outputs. The adjoint certificate theorem supplies its entropy hypotheses
from the Kraus formula, without assuming trace duality or positivity.
-/

noncomputable section

namespace Nonadditivity.Channels.KrausChannel

open Nonadditivity Entropy AdjointPurity
open scoped Matrix.Norms.L2Operator

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ο] [DecidableEq ο] [Fintype κ]

def outputs (T : KrausChannel ι ο κ) : Set (DensityMatrix ο) := Set.range T.output

def minimumEntropy (T : KrausChannel ι ο κ) : ℝ :=
  StateEnsembles.minimumEntropy T.outputs

def holevo (T : KrausChannel ι ο κ) : ℝ := StateEnsembles.quantity T.outputs

theorem outputs_nonempty [Nonempty ι] (T : KrausChannel ι ο κ) : T.outputs.Nonempty :=
  ⟨T.output (maximallyMixed ι), maximallyMixed ι, rfl⟩



theorem holevo_le_of_output_entropy [Nonempty ι] [Nonempty ο]
    (T : KrausChannel ι ο κ) {s : ℝ}
    (hentropy : ∀ ρ : DensityMatrix ι, s ≤ (T.output ρ).vonNeumann) :
    T.holevo ≤ Real.log (Fintype.card ο) - s := by
  apply StateEnsembles.quantity_le T.outputs_nonempty
  rintro _ ⟨ρ, rfl⟩
  exact hentropy ρ



/-- A norm certificate for the concrete Kraus adjoint controls every output
purity and von Neumann entropy. All matrix duality conditions are discharged. -/
theorem output_purity_and_entropy_of_certificate [Nonempty ο]
    (T : KrausChannel ι ο κ) {t : ℝ} (ht : 0 ≤ t)
    (hcertificate : ∀ A : Matrix ο ο ℂ, A.IsHermitian → A.trace = 0 →
      ‖T.adjointMap A‖ ≤ t * hsLength A) (ρ : DensityMatrix ι) :
    (T.output ρ).purity ≤ 1 / (Fintype.card ο : ℝ) + t ^ 2 ∧
      Real.log (Fintype.card ο) - Real.log (1 + (Fintype.card ο : ℝ) * t ^ 2) ≤
        (T.output ρ).vonNeumann := by
  apply purity_and_entropy_of_adjoint_certificate ρ (T.output ρ)
    T.adjointLinearMap ht
  · exact T.adjointMap_isHermitian
  · intro A _ _
    exact T.trace_duality ρ.matrix A
  · exact hcertificate



end Nonadditivity.Channels.KrausChannel


