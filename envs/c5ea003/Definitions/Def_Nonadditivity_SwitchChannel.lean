-- Prove2me | Definitions.Def_Nonadditivity_SwitchChannel
-- name    : Nonadditivity_SwitchChannel
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:35:29.888958+00:00
-- url     : https://prove2.me/theorems/4952dd3f-a11b-4441-b45b-34397811adc8
-- title:
--   A classical switch between a channel and its conjugate
-- statement:
--   For a finite Kraus channel $T$, the switched channel measures a Boolean input label, applies $T$ or its complex conjugate, and discards that label. It is constructed from an explicit finite Kraus family. The supplied output and entropy identities show that switching preserves minimum output entropy and provide the Holevo formula after a Weyl extension.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/SwitchChannel.lean#L29-L96

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_ChannelEntropy
import Definitions.Def_Nonadditivity_ChannelExtensions
import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_ConditionalStates
import Definitions.Def_Nonadditivity_ConjugateChannel
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_EntropyMixtures
import Definitions.Def_Nonadditivity_EntropyProducts
import Definitions.Def_Nonadditivity_QuantumHolevo
import Definitions.Def_Nonadditivity_StateEnsembles
import Definitions.Def_Nonadditivity_Weyl
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




/-!
# The actual two-branch switch channel

The classical input bit is measured and discarded. Its branches are a
concrete Kraus channel and its entrywise conjugate. The original outputs
remain reachable, and entropy concavity prevents arbitrary switch inputs
from lowering the minimum output entropy. Weyl extension then turns this
actual minimum output entropy into the single-use Holevo quantity.
-/

noncomputable section

namespace Nonadditivity.Channels.KrausChannel

open Nonadditivity Entropy
open scoped BigOperators Matrix ComplexOrder

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι]
variable [Fintype ο] [DecidableEq ο] [Fintype κ]

/-- Measure a bit, apply the original or conjugate channel, discard the bit. -/
def switch (T : KrausChannel ι ο κ) : KrausChannel (Bool × ι) ο (Bool × κ) :=
  controlled (fun b : Bool => if b then T.conjugate else T)

/-- The original channel is the false-labelled branch of the actual switch. -/
@[simp] theorem switch_output_false (T : KrausChannel ι ο κ) (ρ : DensityMatrix ι) :
    T.switch.output (labelledState false ρ) = T.output ρ := by
  simp [switch]

/-- The conjugate channel is the true-labelled branch of the actual switch. -/
@[simp] theorem switch_output_true (T : KrausChannel ι ο κ) (ρ : DensityMatrix ι) :
    T.switch.output (labelledState true ρ) = T.conjugate.output ρ := by
  simp [switch]



/-- Arbitrary switch inputs retain every uniform entropy lower bound of the
original channel, including superpositions and entangled control inputs. -/
theorem switch_output_entropy_lower [Nonempty ι]
    (T : KrausChannel ι ο κ) {s : ℝ}
    (hentropy : ∀ ρ : DensityMatrix ι, s ≤ (T.output ρ).vonNeumann)
    (ρ : DensityMatrix (Bool × ι)) : s ≤ (T.switch.output ρ).vonNeumann := by
  unfold switch
  apply controlled_output_entropy_lower
  intro b σ
  cases b
  · exact hentropy σ
  · change s ≤ (T.conjugate.output σ).vonNeumann
    rw [T.conjugate_output_entropy_all]
    exact hentropy σ.conjugate



/-- The switch has exactly the original channel's minimum output entropy.
The argument uses infima and does not assume existence of a minimizing input. -/
theorem switch_minimumEntropy [Nonempty ι] (T : KrausChannel ι ο κ) :
    T.switch.minimumEntropy = T.minimumEntropy := by
  apply le_antisymm
  · unfold minimumEntropy
    apply le_csInf (T.outputs_nonempty.image _)
    rintro _ ⟨σ, ⟨ρ, rfl⟩, rfl⟩
    exact StateEnsembles.minimumEntropy_le
      (outputs := T.switch.outputs) ⟨labelledState false ρ, T.switch_output_false ρ⟩
  · unfold minimumEntropy
    apply le_csInf (T.switch.outputs_nonempty.image _)
    rintro _ ⟨σ, ⟨ρ, rfl⟩, rfl⟩
    apply T.switch_output_entropy_lower
    intro τ
    exact StateEnsembles.minimumEntropy_le (outputs := T.outputs) ⟨τ, rfl⟩

/-- The concrete switch followed by a concrete Weyl extension has the exact
Holevo/minimum-output-entropy relation used in the manuscript. -/
theorem switch_weylExtension_holevo {d : ℕ} [NeZero d] [Nonempty ι]
    (T : KrausChannel ι (ZMod d) κ) :
    T.switch.weylExtension.holevo = Real.log d - T.minimumEntropy := by
  rw [weylExtension_holevo, switch_minimumEntropy]

end Nonadditivity.Channels.KrausChannel


