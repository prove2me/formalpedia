-- Prove2me | Definitions.Def_Nonadditivity_DeterministicQualitative
-- name    : Nonadditivity_DeterministicQualitative
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T21:06:19.553251+00:00
-- url     : https://prove2.me/theorems/2ba70ff1-a410-495e-be09-b15d33113fe2
-- title:
--   Unconditional finite-channel entropy bounds and dimensions
-- statement:
--   For integers $K\ge2$, $n\ge1$, and every $\eta>0$, there are a genuine finite Kraus CPTP channel $T$ and an integer local dimension $N>0$ such that
--   $$\dim\operatorname{Input}(T)=2N^nK^{2n},\qquad\dim\operatorname{Output}(T)=K^n,$$
--   $$0<\chi(T)\le n\log_2(1+9/K)+\eta,\qquad\chi_2(T)\ge\frac{n\log_2K}{K}-\eta.$$
--   Here $\chi(T)$ is one-use Holevo information in bits, and $\chi_2(T)=\chi(T\otimes\overline T)$ is the paired two-use Holevo information. The bundle also gives the same information bounds with dimensions omitted. The finite local dimension is existential rather than sharply bounded. These unconditional deterministic construction estimates provide the common channel witnesses used by the asymptotic gap argument.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/DeterministicQualitative.lean#L31-L92

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








/-! # Unconditional qualitative finite-channel realization

Finite quotients match the required free trace moments exactly. An invertible
input damping suppresses the exceptional spectral subspaces, and its normalized
trace loss controls the Bell entropy. Both Holevo errors may be made arbitrarily
small. No Haar convergence or quantitative random-matrix estimate is assumed.

The two-use lower bound includes a freely prescribed error. This does not assert
the manuscript's exact no-error lower bound or its sharp local matrix dimension.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace Nonadditivity.DeterministicQualitative
open Entropy Channels Channels.KrausChannel AdjointPurity BlockConstruction
open Conversion BlockScalars ActualConsequences FiniteBlockModel
open scoped Matrix.Norms.L2Operator ComplexOrder MatrixOrder

/-- Actual finite CPTP channels with both qualitative estimates and the genuine
input/output dimensions. The local dimension is finite but is not sharply bounded. -/
theorem exists_actual_channel_bounds_with_dimensions {K n : ℕ}
    (hK : 2 ≤ K) (hn : 1 ≤ n) {η : ℝ} (hη : 0 < η) :
    ∃ (T : FiniteQuantumChannel) (N : ℕ), 0 < N ∧
      Fintype.card T.Input = 2 * N^n * K^(2*n) ∧
      Fintype.card T.Output = K^n ∧
      0 < T.chi ∧ T.chi ≤ (n : ℝ)*Scalar.aK K+η ∧
      (n : ℝ)*Scalar.log2 K/(K : ℝ)-η ≤ T.chiTwo := by
  classical
  letI : NeZero K := ⟨by omega⟩
  let ε : ℝ := η * Real.log 2
  have hε : 0 < ε := mul_pos hη Scalar.log_two_pos
  obtain ⟨δ,hδ,hstable⟩ := EntropyStability.exists_damped_bell_entropy_modulus
    (ο := ZMod (K^n)) ε hε
  obtain ⟨p,hp,horder⟩ := DampedRealization.exists_moment_order
    (ο := ZMod (K^n)) (amplification_gt_one hε) (collinsYounConstant_pos hK hn) hδ
  let U := baseUnitary K (4*p)
  let B := blockChannel U n
  obtain ⟨F,G,hF,hres,hGF,hcert,hloss⟩ := horder _ _ B (by
    intro A _ ht hu
    exact block_adjoint_normalized_moment_le hK hn p A ht hu.le)
  let D := DampedChannel.damped B F hF hres
  letI : DecidableEq ((ZMod (K^n) × ZMod (K^n)) ×
      (Bool × TensorChainIndex (LocalIndex K (4*p)) n)) := instDecidableEqProd
  let T := converted D
  have hsingle : T.holevo ≤ (n : ℝ)*Real.log (1+9/(K : ℝ))+ε := by
    have h := converted_holevo_le_of_adjoint_certificate D
      (amplification_times_constant_pos (η := ε) hK hn).le hcert
    simp only [Nat.cast_pow] at h
    exact h.trans (log_purity_factor_le_eta hK hε)
  have hb := CanonicalBlockBell.block_channel_canonical_entropy_le U n
  have hd := hstable B F hF hres hloss
  have hjoint : ((D.tensor D.conjugate).output BellOutput.bellState).vonNeumann ≤
      (n : ℝ)*(2*Real.log K-Real.log K/(K : ℝ))+ε := by
    exact hd.trans (add_le_add hb (le_refl ε))
  have hpair := converted_tensor_holevo_lower D BellOutput.bellState
  have hlower : (n : ℝ)*Real.log K/(K : ℝ)-ε ≤ (T.tensor T).holevo := by
    have hc := two_use_entropy_cancellation K n
    linarith
  have hpos : 0 < T.holevoBits := DampedPositivity.converted_damped_block_holevoBits_pos
    hK U hn F G hF hres hGF
  refine ⟨FiniteQuantumChannel.ofKraus T, Fintype.card (LocalIndex K (4*p)),
    Fintype.card_pos, ?_, ?_, hpos, ?_, ?_⟩
  · exact Qualitative.constructed_input_dimension (LocalIndex K (4*p)) n
  · exact ZMod.card _
  · exact HolevoBits.natural_upper_to_bits n hsingle
  · have h := div_le_div_of_nonneg_right hlower Scalar.log_two_pos.le
    change (n : ℝ)*Scalar.log2 K/(K : ℝ)-η ≤ (T.tensor T).holevo / Real.log 2
    convert h using 1
    dsimp [Scalar.log2, ε]
    field_simp

/-- Unconditional channel bounds in bits. In particular, no analytic input
structure, convergence premise, or assumed channel certificate occurs here. -/
theorem exists_actual_channel_bounds_positive {K n : ℕ}
    (hK : 2 ≤ K) (hn : 1 ≤ n) {η : ℝ} (hη : 0 < η) :
    ∃ T : FiniteQuantumChannel,
      0 < T.chi ∧ T.chi ≤ (n : ℝ)*Scalar.aK K+η ∧
      (n : ℝ)*Scalar.log2 K/(K : ℝ)-η ≤ T.chiTwo := by
  obtain ⟨T,_,_,_,_,h⟩ := exists_actual_channel_bounds_with_dimensions hK hn hη
  exact ⟨T,h⟩

end Nonadditivity.DeterministicQualitative


