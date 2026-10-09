-- Prove2me | solution 1 for Nonadditivity.DeterministicConsequences.actual_vanishing_diverging
-- status  : ACCEPTED   (prove)
-- author  : @JWang226
-- created : 2026-10-07T21:18:22.320533+00:00
-- url     : https://prove2.me/submissions/0a1ec838-f1ac-4fb6-b0ec-0950ee009e82

import Definitions.Def_Nonadditivity_ActualConsequences
import Definitions.Def_Nonadditivity_AdjointPurity
import Definitions.Def_Nonadditivity_Asymptotics
import Definitions.Def_Nonadditivity_BellOutput
import Definitions.Def_Nonadditivity_BlockBell
import Definitions.Def_Nonadditivity_BlockConstruction
import Definitions.Def_Nonadditivity_BlockScalars
import Definitions.Def_Nonadditivity_CanonicalBlockBell
import Definitions.Def_Nonadditivity_ChannelEntropy
import Definitions.Def_Nonadditivity_ChannelExtensions
import Definitions.Def_Nonadditivity_ChannelReindex
import Definitions.Def_Nonadditivity_ChannelTensorControl
import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_CollinsYoun
import Definitions.Def_Nonadditivity_CollinsYounProduct
import Definitions.Def_Nonadditivity_CollinsYounTensor
import Definitions.Def_Nonadditivity_ComplementaryAdjoint
import Definitions.Def_Nonadditivity_ConditionalStates
import Definitions.Def_Nonadditivity_ConjugateChannel
import Definitions.Def_Nonadditivity_Conversion
import Definitions.Def_Nonadditivity_DampedBellStability
import Definitions.Def_Nonadditivity_DampedChannel
import Definitions.Def_Nonadditivity_DampedPositivity
import Definitions.Def_Nonadditivity_DampedRealization
import Definitions.Def_Nonadditivity_DampingNet
import Definitions.Def_Nonadditivity_DeterministicConsequences
import Definitions.Def_Nonadditivity_DeterministicQualitative
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_EntropyContinuity
import Definitions.Def_Nonadditivity_EntropyMixtures
import Definitions.Def_Nonadditivity_EntropyProducts
import Definitions.Def_Nonadditivity_EntropyStability
import Definitions.Def_Nonadditivity_FiniteBlockModel
import Definitions.Def_Nonadditivity_FiniteFreeModel
import Definitions.Def_Nonadditivity_FiniteMomentMatching
import Definitions.Def_Nonadditivity_FiniteRealization
import Definitions.Def_Nonadditivity_FiniteRegularMatrix
import Definitions.Def_Nonadditivity_FiniteSetFactorization
import Definitions.Def_Nonadditivity_FreeBridge
import Definitions.Def_Nonadditivity_FreeCreation
import Definitions.Def_Nonadditivity_FreeEmbedding
import Definitions.Def_Nonadditivity_FreeModel
import Definitions.Def_Nonadditivity_GeneralBell
import Definitions.Def_Nonadditivity_HaarModel
import Definitions.Def_Nonadditivity_HaarMomentTail
import Definitions.Def_Nonadditivity_HolevoBits
import Definitions.Def_Nonadditivity_HolevoRateLimit
import Definitions.Def_Nonadditivity_HolevoTensorSuperadditivity
import Definitions.Def_Nonadditivity_InitialNetReduction
import Definitions.Def_Nonadditivity_Linearization
import Definitions.Def_Nonadditivity_MatrixRegularRestriction
import Definitions.Def_Nonadditivity_Net
import Definitions.Def_Nonadditivity_NetPolynomial
import Definitions.Def_Nonadditivity_NetPolynomialSupport
import Definitions.Def_Nonadditivity_ObservableDimension
import Definitions.Def_Nonadditivity_PolynomialDilation
import Definitions.Def_Nonadditivity_PolynomialReduction
import Definitions.Def_Nonadditivity_PositiveHolevo
import Definitions.Def_Nonadditivity_ProductPolynomialReduction
import Definitions.Def_Nonadditivity_PureChannelEntropy
import Definitions.Def_Nonadditivity_Qualitative
import Definitions.Def_Nonadditivity_QuantumHolevo
import Definitions.Def_Nonadditivity_RegularCoefficientEnergy
import Definitions.Def_Nonadditivity_RegularDilation
import Definitions.Def_Nonadditivity_RegularFactorization
import Definitions.Def_Nonadditivity_RegularFubini
import Definitions.Def_Nonadditivity_RegularRestriction
import Definitions.Def_Nonadditivity_RegularShiftedDilation
import Definitions.Def_Nonadditivity_RegularizedHolevo
import Definitions.Def_Nonadditivity_Scalar
import Definitions.Def_Nonadditivity_SpectralDamping
import Definitions.Def_Nonadditivity_StateEnsembles
import Definitions.Def_Nonadditivity_StrictEntropy
import Definitions.Def_Nonadditivity_StructuredFiniteChannel
import Definitions.Def_Nonadditivity_StructuredHaarModel
import Definitions.Def_Nonadditivity_StructuredLinearization
import Definitions.Def_Nonadditivity_SwitchChannel
import Definitions.Def_Nonadditivity_TensorPartitionReduction
import Definitions.Def_Nonadditivity_TensorPowers
import Definitions.Def_Nonadditivity_Weyl
import Definitions.Def_Nonadditivity_WeylTensor
import Definitions.Def_Nonadditivity_WordBallReduction
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Subadditive
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Int.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Fintype
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.UniformSpace.HeineCantor

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/










/-!
# Asymptotic consequences of the numerical channel bounds

The sequence `blockLength K = ⌈K / √(ln K)⌉₊` is the actual sequence in
Corollary 4 (vanishing Holevo information and diverging capacity).
The scalar limits below are unconditional theorems of real analysis.
The channel-specific conclusion takes the proved numerical bounds as explicit
hypotheses; it does not assert or axiomatize the random-channel construction.
-/

namespace Nonadditivity.Asymptotics

open Filter Topology

noncomputable section







lemma log_two_pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)









lemma blockLength_div_upper {K : ℕ} (hK : 2 ≤ K) :
    (blockLength K : ℝ) / K ≤
      1 / Real.sqrt (Real.log K) + 1 / (K : ℝ) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hspos : 0 < Real.sqrt (Real.log K) := Real.sqrt_pos.2 (log_nat_pos hK)
  have hc : (blockLength K : ℝ) ≤
      (K : ℝ) / Real.sqrt (Real.log K) + 1 :=
    (Nat.ceil_lt_add_one (div_nonneg (Nat.cast_nonneg K) (Real.sqrt_nonneg _))).le
  apply (div_le_iff₀ hKpos).2
  convert hc using 1
  field_simp



lemma log_sqrt_tendsto_atTop :
    Tendsto (fun K : ℕ => Real.sqrt (Real.log K)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

lemma blockLength_div_tendsto_zero :
    Tendsto (fun K : ℕ => (blockLength K : ℝ) / K) atTop (𝓝 0) := by
  have hs : Tendsto (fun K : ℕ => 1 / Real.sqrt (Real.log K)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop log_sqrt_tendsto_atTop
  have hn : Tendsto (fun K : ℕ => 1 / (K : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall fun K => by positivity)
  · filter_upwards [eventually_ge_atTop 2] with K hK
    exact blockLength_div_upper hK
  · simpa using hs.add hn

/-- The explicit single-use upper bound tends to zero; no limit is assumed. -/
theorem separationUpper_tendsto_zero :
    Tendsto separationUpper atTop (𝓝 0) := by
  have h := blockLength_div_tendsto_zero.const_mul (9 / Real.log 2)
  have hn : Tendsto (fun K : ℕ => 1 / (K : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsum : Tendsto (fun K : ℕ =>
      (9 / Real.log 2) * ((blockLength K : ℝ) / K) + 1 / (K : ℝ)) atTop (𝓝 0) := by
    simpa using h.add hn
  convert hsum using 1
  ext K
  simp only [separationUpper, div_eq_mul_inv, mul_inv_rev]
  ring

lemma separationLower_ge_sqrt {K : ℕ} (hK : 2 ≤ K) :
    Real.sqrt (Real.log K) / (2 * Real.log 2) ≤ separationLower K := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hl := log_nat_pos hK
  have hspos : 0 < Real.sqrt (Real.log K) := Real.sqrt_pos.2 hl
  have hc := Nat.le_ceil ((K : ℝ) / Real.sqrt (Real.log K))
  have hb : (K : ℝ) ≤ (blockLength K : ℝ) * Real.sqrt (Real.log K) :=
    (div_le_iff₀ hspos).1 hc
  have hb' := mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg (Real.log K))
  have hs : Real.sqrt (Real.log K) * Real.sqrt (Real.log K) = Real.log K :=
    Real.mul_self_sqrt hl.le
  have hn : Real.sqrt (Real.log K) * K ≤ (blockLength K : ℝ) * Real.log K := by
    nlinarith [hb', hs]
  unfold separationLower
  apply (div_le_div_iff₀ (by positivity : 0 < 2 * Real.log (2 : ℝ))
    (by positivity : 0 < 2 * (K : ℝ) * Real.log (2 : ℝ))).2
  nlinarith [mul_le_mul_of_nonneg_right hn log_two_pos.le]

/-- The exact rounded lower bound diverges to infinity. -/
theorem separationLower_tendsto_atTop : Tendsto separationLower atTop atTop := by
  have h : Tendsto (fun K : ℕ => Real.sqrt (Real.log K) / (2 * Real.log 2))
      atTop atTop := log_sqrt_tendsto_atTop.atTop_div_const (by positivity)
  refine tendsto_atTop_mono' atTop ?_ h
  filter_upwards [eventually_ge_atTop 2] with K hK
  exact separationLower_ge_sqrt hK



































end

end Nonadditivity.Asymptotics

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/




/-!
# Ensembles of actual quantum states

Every average below is proved positive semidefinite and trace one. The
Holevo quantity is a supremum over normalized finite ensembles of states in
the specified output set. Entropies use natural logarithms.
-/

noncomputable section

namespace Nonadditivity.Entropy

open scoped BigOperators ComplexOrder Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]













end Nonadditivity.Entropy

namespace Nonadditivity.StateEnsembles

open Entropy
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]























theorem quantity_nonneg [Nonempty ι] {outputs : Set (DensityMatrix ι)}
    (hne : outputs.Nonempty) : 0 ≤ quantity outputs := by
  obtain ⟨ρ, hρ⟩ := hne
  have h := le_csSup (information_bddAbove outputs)
    (show (singleton ρ hρ).information ∈ Set.range (fun e : Ensemble outputs => e.information)
      from ⟨singleton ρ hρ, rfl⟩)
  simpa [quantity] using h









end Nonadditivity.StateEnsembles

end

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









theorem holevo_nonneg [Nonempty ι] [Nonempty ο] (T : KrausChannel ι ο κ) :
    0 ≤ T.holevo := StateEnsembles.quantity_nonneg T.outputs_nonempty









end Nonadditivity.Channels.KrausChannel

end

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/




/-!
# The actual channel bounds in the manuscript's base-two convention

The underlying Holevo information is defined on finite ensembles of genuine
quantum output states.  Division by the positive constant `log 2` converts
the proved natural-logarithm results without changing any channel or model.
-/

noncomputable section

namespace Nonadditivity.Channels.KrausChannel

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ο] [DecidableEq ο] [Fintype κ]





theorem holevoBits_nonneg [Nonempty ι] [Nonempty ο] (T : KrausChannel ι ο κ) :
    0 ≤ T.holevoBits :=
  div_nonneg T.holevo_nonneg Scalar.log_two_pos.le



end Nonadditivity.Channels.KrausChannel

namespace Nonadditivity.HolevoBits

open Entropy Channels Channels.KrausChannel AdjointPurity BlockConstruction Conversion Scalar
open scoped Matrix.Norms.L2Operator





variable {K : ℕ} [NeZero K]



end Nonadditivity.HolevoBits

end

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/





/-!
# Asymptotic separation for actual finite quantum channels

The channels in this file are actual finite Kraus CPTP maps. They are chosen
from the proved qualitative realization using the specified normalized Haar
matrix model. The two remaining analytic inputs are displayed explicitly:
Collins--Youn's free-operator bound and the canonical Haar strong convergence
statement. No numerical Holevo family or entropy inequality is assumed.

The quantities here are Holevo information in bits. The file makes no
operational-capacity assertion and requires no coding theorem.
-/

noncomputable section

namespace Nonadditivity.ActualConsequences

open Filter Topology
open Nonadditivity.Entropy Nonadditivity.Channels Nonadditivity.Channels.KrausChannel
open scoped BigOperators Matrix ComplexOrder



attribute [instance] FiniteQuantumChannel.inputFinite FiniteQuantumChannel.inputDecidable
  FiniteQuantumChannel.inputNonempty FiniteQuantumChannel.outputFinite
  FiniteQuantumChannel.outputDecidable FiniteQuantumChannel.outputNonempty
  FiniteQuantumChannel.environmentFinite

namespace FiniteQuantumChannel















theorem chi_nonneg (T : FiniteQuantumChannel) : 0 ≤ T.chi := T.channel.holevoBits_nonneg



end FiniteQuantumChannel

































end Nonadditivity.ActualConsequences

end

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/




/-! Unconditional vanishing single-use information and unbounded additive
nonadditivity for actual finite channels. The fixed-moment finite-group model and
spectral damping supply all analytic inputs. An arbitrarily small slack in the
finite two-use bound suffices for these qualitative limits. -/
noncomputable section
namespace Nonadditivity.DeterministicConsequences
open Filter Topology ActualConsequences
open Channels Channels.KrausChannel





theorem separatingFamily_bounds {K : ℕ} (hK : 2 ≤ K) :
    (separatingFamily K).chi ≤ Asymptotics.separationUpper K ∧
      Asymptotics.separationLower K - 1 ≤ (separatingFamily K).chiTwo / 2 := by
  simp only [separatingFamily,dif_pos hK]
  exact (Classical.choose_spec (exists_actual_separating_channel_positive hK)).2

























end Nonadditivity.DeterministicConsequences

end

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/




/-! Unconditional vanishing single-use information and unbounded additive
nonadditivity for actual finite channels. The fixed-moment finite-group model and
spectral damping supply all analytic inputs. An arbitrarily small slack in the
finite two-use bound suffices for these qualitative limits. -/

open Nonadditivity
open Nonadditivity.DeterministicConsequences
open Filter Topology ActualConsequences
open Channels Channels.KrausChannel

theorem solution :
    Tendsto (fun K => (separatingFamily K).chi) atTop (𝓝 0) ∧
      Tendsto (fun K => (separatingFamily K).chiTwo/2) atTop atTop := by
  constructor
  · apply squeeze_zero' (Eventually.of_forall (fun K => (separatingFamily K).chi_nonneg))
    · filter_upwards [eventually_ge_atTop 2] with K hK
      exact (separatingFamily_bounds hK).1
    · exact Asymptotics.separationUpper_tendsto_zero
  · have hl : Tendsto (fun K => Asymptotics.separationLower K - 1) atTop atTop := by
      simpa only [sub_eq_add_neg] using
        Asymptotics.separationLower_tendsto_atTop.atTop_add
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (𝓝 (-1)))
    refine tendsto_atTop_mono' atTop ?_ hl
    filter_upwards [eventually_ge_atTop 2] with K hK
    exact (separatingFamily_bounds hK).2
