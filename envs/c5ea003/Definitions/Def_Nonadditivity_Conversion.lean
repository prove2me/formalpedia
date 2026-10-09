-- Prove2me | Definitions.Def_Nonadditivity_Conversion
-- name    : Nonadditivity_Conversion
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:36:17.741416+00:00
-- url     : https://prove2.me/theorems/a7c9fb39-5dc5-4561-b2c6-dd3b25a0e2c3
-- title:
--   Switch and Weyl conversion of finite channels
-- statement:
--   For a finite Kraus channel with positive output dimension $d$, the converted channel first switches between the channel and its conjugate and then applies the $d^2$-label Weyl extension. The bundle proves its single-use information identity and upper bounds derived from output entropy or an adjoint certificate, together with two-use information lower bounds obtained from a joint output state. The quantities in these identities use natural logarithms; conversion to bits is supplied separately.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/Conversion.lean#L26-L95

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_ChannelEntropy
import Definitions.Def_Nonadditivity_ChannelExtensions
import Definitions.Def_Nonadditivity_ChannelTensorControl
import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_ConditionalStates
import Definitions.Def_Nonadditivity_ConjugateChannel
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_EntropyMixtures
import Definitions.Def_Nonadditivity_EntropyProducts
import Definitions.Def_Nonadditivity_QuantumHolevo
import Definitions.Def_Nonadditivity_StateEnsembles
import Definitions.Def_Nonadditivity_SwitchChannel
import Definitions.Def_Nonadditivity_Weyl
import Definitions.Def_Nonadditivity_WeylTensor
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/





/-! # Concrete entropy-gap to Holevo-gap conversion

This file applies the checked switch and Weyl constructions to actual
Kraus channels. Its analytic norm-certificate premise remains explicit.
-/

noncomputable section

namespace Nonadditivity.Conversion

open Entropy Channels Channels.KrausChannel AdjointPurity
open scoped Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
variable {d : ℕ} [NeZero d]

/-- The manuscript's switch followed by its `d²`-label Weyl extension. -/
def converted (T : KrausChannel ι (ZMod d) κ) := T.switch.weylExtension

theorem converted_holevo [Nonempty ι] (T : KrausChannel ι (ZMod d) κ) :
    (converted T).holevo = Real.log d - T.minimumEntropy :=
  T.switch_weylExtension_holevo

theorem converted_holevo_le_of_output_entropy [Nonempty ι]
    (T : KrausChannel ι (ZMod d) κ) {s : ℝ}
    (hentropy : ∀ ρ : DensityMatrix ι, s ≤ (T.output ρ).vonNeumann) :
    (converted T).holevo ≤ Real.log d - s := by
  rw [converted_holevo]
  have hmin : s ≤ T.minimumEntropy := by
    apply le_csInf (T.outputs_nonempty.image _)
    rintro _ ⟨_, ⟨ρ, rfl⟩, rfl⟩
    exact hentropy ρ
  linarith

/-- A genuine finite-dimensional channel with the required small single-use
Holevo information, from an adjoint operator/HS certificate for its base. -/
theorem converted_holevo_le_of_adjoint_certificate [Nonempty ι]
    (T : KrausChannel ι (ZMod d) κ) {t : ℝ} (ht : 0 ≤ t)
    (hcertificate : ∀ A : Matrix (ZMod d) (ZMod d) ℂ,
      A.IsHermitian → A.trace = 0 → ‖T.adjointMap A‖ ≤ t * hsLength A) :
    (converted T).holevo ≤ Real.log (1 + (d : ℝ) * t ^ 2) := by
  have h := converted_holevo_le_of_output_entropy T
    (fun ρ => (T.output_purity_and_entropy_of_certificate ht hcertificate ρ).2)
  simp only [ZMod.card] at h
  linarith



/-- Independent Weyl labels turn any joint output into a real finite coding
ensemble, even when the underlying input is entangled. -/
theorem weyl_tensor_holevo_lower {μ η : Type*} [Fintype μ] [DecidableEq μ] [Fintype η]
    (T : KrausChannel ι (ZMod d) κ) (S : KrausChannel μ (ZMod d) η)
    (ρ : DensityMatrix (ι × μ)) :
    2 * Real.log d - ((T.tensor S).output ρ).vonNeumann ≤
      (T.weylExtension.tensor S.weylExtension).holevo := by
  apply WeylTensor.orbit_information_lower_bound
    (T.weylExtension.tensor S.weylExtension).outputs ((T.tensor S).output ρ)
  intro q r
  refine ⟨jointLabelledState q r ρ, ?_⟩
  change ((controlled (fun q => T.outputUnitary (Weyl.family q))).tensor
    (controlled (fun r => S.outputUnitary (Weyl.family r)))).output
      (jointLabelledState q r ρ) = _
  rw [controlled_tensor_output_labelled, tensor_outputUnitary_output]
  rfl

/-- The two switches reproduce the original/conjugate pair on an arbitrary
entangled input; independent Weyl ensembles then give the two-use lower bound. -/
theorem converted_tensor_holevo_lower (T : KrausChannel ι (ZMod d) κ)
    (ρ : DensityMatrix (ι × ι)) :
    2 * Real.log d - ((T.tensor T.conjugate).output ρ).vonNeumann ≤
      ((converted T).tensor (converted T)).holevo := by
  have h := weyl_tensor_holevo_lower T.switch T.switch (jointLabelledState false true ρ)
  have ho : (T.switch.tensor T.switch).output (jointLabelledState false true ρ) =
      (T.tensor T.conjugate).output ρ := by
    change ((controlled (fun b : Bool => if b then T.conjugate else T)).tensor
      (controlled (fun b : Bool => if b then T.conjugate else T))).output _ = _
    rw [controlled_tensor_output_labelled]
    rfl
  rw [ho] at h
  exact h





end Nonadditivity.Conversion


