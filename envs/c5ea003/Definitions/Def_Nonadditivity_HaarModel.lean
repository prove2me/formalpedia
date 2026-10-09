-- Prove2me | Definitions.Def_Nonadditivity_HaarModel
-- name    : Nonadditivity_HaarModel
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:43:21.278976+00:00
-- url     : https://prove2.me/theorems/161e0961-f87e-47b4-9198-e464030b133d
-- title:
--   Finite products of normalized Haar unitary measures
-- statement:
--   For integers $K,n,N\ge0$, let $\mathcal U_N=U(N+1)$ be the unitary group of complex matrices indexed by $\{0,\ldots,N\}$. It is equipped with its Borel measurable structure, compact topology, and normalized Haar probability measure $\mu_N$. Define the sample space and joint law by
--   $$\Omega_{K,n,N}=\mathcal U_N^{\{0,\ldots,n-1\}\times\{0,\ldots,K-1\}},\qquad \mathbb P_{K,n,N}=\bigotimes_{(j,a)}\mu_N.$$
--   Thus each block/branch pair receives an independent Haar unitary. The sample-unitary map agrees with these values on the first $n$ legs and extends by the identity for later leg indices. The bundle establishes the measurable, compact, Haar-invariance, and probability instances needed to interpret this finite sampling model.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/HaarModel.lean#L29-L83

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
import Definitions.Def_Nonadditivity_ComplementaryAdjoint
import Definitions.Def_Nonadditivity_ConditionalStates
import Definitions.Def_Nonadditivity_ConjugateChannel
import Definitions.Def_Nonadditivity_Conversion
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_EntropyMixtures
import Definitions.Def_Nonadditivity_EntropyProducts
import Definitions.Def_Nonadditivity_FiniteRealization
import Definitions.Def_Nonadditivity_FreeBridge
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_Net
import Definitions.Def_Nonadditivity_PureChannelEntropy
import Definitions.Def_Nonadditivity_Qualitative
import Definitions.Def_Nonadditivity_QuantumHolevo
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
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Star.Unitary

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/








/-! # The canonical independent Haar unitary sampling model

The probability spaces and their unitary random variables are constructed
here. Strong convergence is the remaining explicit analytic proposition,
formulated for these concrete sampled block channels.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Nonadditivity.HaarModel

open MeasureTheory ProbabilityTheory Channels.KrausChannel BlockConstruction Entropy
open scoped Matrix Topology

/-- The finite unitary group in local dimension `N+1`. -/
abbrev LocalUnitary (N : ℕ) := unitary (Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)

open scoped Matrix.Norms.Elementwise in
instance localUnitaryCompact (N : ℕ) : CompactSpace (LocalUnitary N) := by
  apply isCompact_iff_compactSpace.mp
  exact Metric.isCompact_of_isClosed_isBounded isClosed_unitary
    (isBounded_iff_forall_norm_le.mpr ⟨1, fun U hU =>
      entrywise_sup_norm_bound_of_unitary hU⟩)

open scoped Matrix.Norms.L2Operator

instance localUnitaryMeasurable (N : ℕ) : MeasurableSpace (LocalUnitary N) :=
  borel (LocalUnitary N)

instance localUnitaryBorel (N : ℕ) : BorelSpace (LocalUnitary N) := ⟨rfl⟩

/-- Normalized Haar measure on the compact complex unitary group. -/
def haar (N : ℕ) : Measure (LocalUnitary N) := Measure.haarMeasure ⊤

instance haarProbability (N : ℕ) : IsProbabilityMeasure (haar N) := by
  constructor
  exact Measure.haarMeasure_self

instance haarInvariant (N : ℕ) : Measure.IsHaarMeasure (haar N) := by
  unfold haar
  infer_instance

/-- One independent Haar unitary for every block/branch pair. -/
abbrev Sample (K n N : ℕ) := (Fin n × Fin K) → LocalUnitary N

/-- The actual joint law, the finite product of normalized Haar measures. -/
def sampleMeasure (K n N : ℕ) : Measure (Sample K n N) :=
  Measure.pi (fun _ => haar N)

instance sampleProbability (K n N : ℕ) : IsProbabilityMeasure (sampleMeasure K n N) := by
  unfold sampleMeasure
  infer_instance





/-- Extend the sampled blocks by identities beyond the fixed block length. -/
def sampleUnitary (K n N : ℕ) (ω : Sample K n N) (j : ℕ) (a : Fin K) :
    LocalUnitary N :=
  if h : j < n then ω (⟨j, h⟩, a) else 1







variable {K : ℕ} [NeZero K]











end Nonadditivity.HaarModel


