-- Prove2me | Definitions.Def_Nonadditivity_DeterministicConsequences
-- name    : Nonadditivity_DeterministicConsequences
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T21:10:02.387993+00:00
-- url     : https://prove2.me/theorems/77449662-8d13-49e3-9332-91b8b70808e4
-- title:
--   A selected family of genuine finite separating channels
-- statement:
--   For each integer $K\ge2$, define
--   $$n_K=\left\lceil\frac{K}{\sqrt{\ln K}}\right\rceil,\qquad u_K=\frac{9n_K}{K\ln2}+\frac1K,\qquad l_K=\frac{n_K\ln K}{2K\ln2}.$$
--   The deterministic construction supplies a finite Kraus CPTP channel $T_K$ with
--   $$0<\chi(T_K)\le u_K,\qquad \frac{\chi_2(T_K)}2\ge l_K-1.$$
--   The bundle selects one such channel for every $K\ge2$ and uses the one-dimensional identity channel for $K=0,1$, giving a total family indexed by natural numbers. Holevo quantities are measured in bits, and $\chi_2(T)=\chi(T\otimes\overline T)$. The selected family is the concrete witness sequence underlying the mission's separate vanishing-information, unbounded-gap, and common-witness theorem nodes.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/DeterministicConsequences.lean#L18-L45

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




/-! Unconditional vanishing single-use information and unbounded additive
nonadditivity for actual finite channels. The fixed-moment finite-group model and
spectral damping supply all analytic inputs. An arbitrarily small slack in the
finite two-use bound suffices for these qualitative limits. -/
noncomputable section
namespace Nonadditivity.DeterministicConsequences
open Filter Topology ActualConsequences
open Channels Channels.KrausChannel

/-- Actual finite channels with the integer `sqrt(log)` block length. -/
theorem exists_actual_separating_channel_positive {K : ℕ} (hK : 2 ≤ K) :
    ∃ T : FiniteQuantumChannel, 0 < T.chi ∧ T.chi ≤ Asymptotics.separationUpper K ∧
      Asymptotics.separationLower K - 1 ≤ T.chiTwo / 2 := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hn : 1 ≤ Asymptotics.blockLength K := Asymptotics.blockLength_pos hK
  obtain ⟨T,hpos,h₁,h₂⟩ := DeterministicQualitative.exists_actual_channel_bounds_positive hK hn
    (show 0 < 1/(K : ℝ) by positivity)
  refine ⟨T,hpos,?_,?_⟩
  · calc
      T.chi ≤ (Asymptotics.blockLength K : ℝ)*Scalar.aK K + 1/(K : ℝ) := h₁
      _ ≤ (Asymptotics.blockLength K : ℝ)*(9/((K : ℝ)*Real.log 2)) + 1/(K : ℝ) := by
        have hh := mul_le_mul_of_nonneg_left (Scalar.aK_le hKpos)
          (Nat.cast_nonneg (Asymptotics.blockLength K) : (0 : ℝ) ≤ Asymptotics.blockLength K)
        linarith
      _ = Asymptotics.separationUpper K := by unfold Asymptotics.separationUpper; ring
  · have hraw : 2*Asymptotics.separationLower K - 1/(K : ℝ) ≤ T.chiTwo := by
      convert h₂ using 1
      unfold Asymptotics.separationLower Scalar.log2
      ring
    have hKtwo : (2 : ℝ) ≤ K := by exact_mod_cast hK
    have hi : 1/(K : ℝ) ≤ 2 := (div_le_iff₀ hKpos).mpr (by linarith)
    linarith

/-- A sequence of genuine finite Kraus CPTP maps, selected from the proved construction. -/
def separatingFamily (K : ℕ) : FiniteQuantumChannel :=
  if hK : 2 ≤ K then Classical.choose (exists_actual_separating_channel_positive hK)
  else FiniteQuantumChannel.ofKraus (KrausChannel.identity : KrausChannel (Fin 1) (Fin 1) Unit)



























end Nonadditivity.DeterministicConsequences


