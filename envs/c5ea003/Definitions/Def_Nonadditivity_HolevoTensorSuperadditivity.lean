-- Prove2me | Definitions.Def_Nonadditivity_HolevoTensorSuperadditivity
-- name    : Nonadditivity_HolevoTensorSuperadditivity
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:43:42.845045+00:00
-- url     : https://prove2.me/theorems/448dfc26-0056-4952-a558-0271540d3b1d
-- title:
--   Basis relabeling preserves ensemble and channel Holevo information
-- statement:
--   A finite basis equivalence relabels every state in a normalized ensemble, commutes with its weighted average, and preserves its Holevo information. Applying the inverse equivalence recovers the original state and ensemble information. The correspondence preserves the supremum over all finite ensembles, and therefore preserves a channel's single-use Holevo information under input and output basis relabeling, in either natural-logarithm units or bits.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/HolevoTensorSuperadditivity.lean#L57-L244

import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_BellOutput
import Definitions.Def_Nonadditivity_BlockBell
import Definitions.Def_Nonadditivity_BlockConstruction
import Definitions.Def_Nonadditivity_BlockScalars
import Definitions.Def_Nonadditivity_ChannelEntropy
import Definitions.Def_Nonadditivity_ChannelExtensions
import Definitions.Def_Nonadditivity_ChannelReindex
import Definitions.Def_Nonadditivity_ChannelTensorControl
import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_ConditionalStates
import Definitions.Def_Nonadditivity_ConjugateChannel
import Definitions.Def_Nonadditivity_Conversion
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_EntropyMixtures
import Definitions.Def_Nonadditivity_EntropyProducts
import Definitions.Def_Nonadditivity_FiniteRealization
import Definitions.Def_Nonadditivity_FreeBridge
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_HolevoBits
import Definitions.Def_Nonadditivity_Net
import Definitions.Def_Nonadditivity_PureChannelEntropy
import Definitions.Def_Nonadditivity_Qualitative
import Definitions.Def_Nonadditivity_QuantumHolevo
import Definitions.Def_Nonadditivity_Scalar
import Definitions.Def_Nonadditivity_StateEnsembles
import Definitions.Def_Nonadditivity_SwitchChannel
import Definitions.Def_Nonadditivity_TensorPowers
import Definitions.Def_Nonadditivity_Weyl
import Definitions.Def_Nonadditivity_WeylTensor
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/



/-! # Holevo superadditivity for genuine tensor-product channels

Product ensembles give the information sum, using the proved entropy identity
for actual product density matrices. No entropy or Holevo additivity premise is
used. Basis changes and Kraus relabeling preserve the Holevo supremum.
-/

noncomputable section

namespace Nonadditivity

open Entropy Channels Channels.KrausChannel
open scoped BigOperators Kronecker Matrix

namespace StateEnsembles

variable {ι μ : Type*} [Fintype ι] [DecidableEq ι] [Fintype μ] [DecidableEq μ]







/-- Relabel all output states of an ensemble by the same basis equivalence. -/
def Ensemble.reindex {outputs : Set (DensityMatrix ι)} (e : Ensemble outputs)
    (u : ι ≃ μ) : Ensemble ((fun ρ => ρ.reindex u) '' outputs) where
  size := e.size
  weight := e.weight
  weight_nonneg := e.weight_nonneg
  weight_sum := e.weight_sum
  state := fun a => (e.state a).reindex u
  state_mem := fun a => ⟨e.state a, e.state_mem a, rfl⟩

theorem Ensemble.reindex_average {outputs : Set (DensityMatrix ι)}
    (e : Ensemble outputs) (u : ι ≃ μ) :
    (e.reindex u).average = e.average.reindex u := by
  apply DensityMatrix.ext
  ext a b
  simp only [Ensemble.average, Ensemble.reindex, DensityMatrix.mixture_matrix,
    DensityMatrix.reindex, Matrix.reindex_apply, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.submatrix_apply]

@[simp] theorem Ensemble.reindex_information {outputs : Set (DensityMatrix ι)}
    (e : Ensemble outputs) (u : ι ≃ μ) : (e.reindex u).information = e.information := by
  unfold Ensemble.information
  rw [Ensemble.reindex_average, DensityMatrix.reindex_entropy]
  simp only [Ensemble.reindex, DensityMatrix.reindex_entropy]
  rfl

@[simp] theorem density_reindex_symm (ρ : DensityMatrix ι) (u : ι ≃ μ) :
    (ρ.reindex u).reindex u.symm = ρ := by
  apply DensityMatrix.ext
  ext a b
  simp [DensityMatrix.reindex, Matrix.reindex_apply]

theorem quantity_reindex_le [Nonempty ι] [Nonempty μ]
    {outputs : Set (DensityMatrix ι)} (hne : outputs.Nonempty) (u : ι ≃ μ) :
    quantity outputs ≤ quantity ((fun ρ => ρ.reindex u) '' outputs) := by
  apply csSup_le
  · obtain ⟨ρ, hρ⟩ := hne
    exact ⟨_, singleton ρ hρ, rfl⟩
  · rintro _ ⟨e, rfl⟩
    change e.information ≤ _
    rw [← e.reindex_information u]
    exact le_csSup (information_bddAbove _) ⟨e.reindex u, rfl⟩

/-- The ensemble supremum is exactly invariant under an output basis change. -/
theorem quantity_reindex [Nonempty ι] [Nonempty μ]
    {outputs : Set (DensityMatrix ι)} (hne : outputs.Nonempty) (u : ι ≃ μ) :
    quantity ((fun ρ => ρ.reindex u) '' outputs) = quantity outputs := by
  apply le_antisymm
  · have h := quantity_reindex_le (hne.image ((fun ρ => ρ.reindex u))) u.symm
    have he : ((fun ρ => ρ.reindex u.symm) '' ((fun ρ => ρ.reindex u) '' outputs)) =
        outputs := by
      ext ρ
      constructor
      · rintro ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩
        simpa using hσ
      · intro hρ
        exact ⟨ρ.reindex u, ⟨ρ, hρ, rfl⟩, density_reindex_symm ρ u⟩
    rwa [he] at h
  · exact quantity_reindex_le hne u

end StateEnsembles

namespace Channels.KrausChannel

variable {ι ο κ μ ν η : Type*}
variable [Fintype ι] [DecidableEq ι] [Fintype ο] [DecidableEq ο] [Fintype κ]
variable [Fintype μ] [DecidableEq μ] [Fintype ν] [DecidableEq ν] [Fintype η]











/-- Equivalent input/output bases do not change the Holevo quantity. -/
theorem holevo_reindex [Nonempty ι] [Nonempty ο] [Nonempty μ] [Nonempty ν]
    (T : KrausChannel ι ο κ) (ei : ι ≃ μ) (eo : ο ≃ ν) :
    (T.reindex ei eo).holevo = T.holevo := by
  have he : (T.reindex ei eo).outputs = (fun ρ => ρ.reindex eo) '' T.outputs := by
    ext σ
    constructor
    · rintro ⟨ρ, rfl⟩
      refine ⟨T.output (ρ.reindex ei.symm), ⟨_, rfl⟩, ?_⟩
      apply DensityMatrix.ext
      have h := T.reindex_map ei eo (ρ.reindex ei.symm).matrix
      simpa [DensityMatrix.reindex, Matrix.reindex_apply] using h.symm
    · rintro ⟨_, ⟨ρ, rfl⟩, rfl⟩
      refine ⟨ρ.reindex ei, ?_⟩
      apply DensityMatrix.ext
      exact T.reindex_map ei eo ρ.matrix
  unfold holevo
  rw [he, StateEnsembles.quantity_reindex T.outputs_nonempty eo]



@[simp] theorem holevoBits_reindex
    [Nonempty ι] [Nonempty ο] [Nonempty μ] [Nonempty ν]
    (T : KrausChannel ι ο κ) (ei : ι ≃ μ) (eo : ο ≃ ν) :
    (T.reindex ei eo).holevoBits = T.holevoBits := by rw [holevoBits, holevo_reindex]; rfl



end Channels.KrausChannel
end Nonadditivity


