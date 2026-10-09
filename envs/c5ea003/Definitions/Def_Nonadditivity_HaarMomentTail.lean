-- Prove2me | Definitions.Def_Nonadditivity_HaarMomentTail
-- name    : Nonadditivity_HaarMomentTail
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:44:19.189983+00:00
-- url     : https://prove2.me/theorems/376941aa-aabb-48ce-98a5-1bb25985a720
-- title:
--   Even trace moments dominate Hermitian operator norm
-- statement:
--   Let $A$ be a Hermitian complex matrix on a finite index set, with real eigenvalues $\lambda_i$. For every integer $q\ge0$, its trace moment satisfies
--   $$\operatorname{Re}\operatorname{Tr}(A^q)=\sum_i\lambda_i^q.$$
--   If the index set is nonempty, then for every integer $p\ge0$,
--   $$\|A\|^{2p}\le\operatorname{Re}\operatorname{Tr}(A^{2p}),$$
--   where $\|A\|$ is the Euclidean operator norm. These deterministic spectral identities are the imported part of the moment-tail module. They allow even trace-moment bounds to control the magnitude of a Hermitian observable.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/HaarMomentTail.lean#L29-L63

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
import Definitions.Def_Nonadditivity_HaarModel
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
import Mathlib.Analysis.CStarAlgebra.Spectrum
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
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
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





/-! # Actual trace moments control operator-norm upper tails

The matrix norm throughout is the Euclidean operator norm. The moment is
the literal (unnormalized) matrix trace. These results prove the elementary
last step of the high-moment method; they do not supply the Haar high-moment
estimate, which remains the random-matrix input.
-/

noncomputable section

namespace Nonadditivity.HaarMomentTail

open MeasureTheory Filter
open scoped Matrix Matrix.Norms.L2Operator Topology ENNReal

set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The trace of any power, computed using the actual Hermitian spectral theorem. -/
theorem trace_pow_re_eq_sum (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (q : ℕ) :
    (A ^ q).trace.re = ∑ i, hA.eigenvalues i ^ q := by
  let U := hA.eigenvectorUnitary
  let D := Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))
  have hs : A = Unitary.conjStarAlgAut ℂ _ U D := hA.spectral_theorem
  have ht : (A ^ q).trace = (D ^ q).trace := by
    rw [hs, ← map_pow, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, Matrix.one_mul]
  rw [ht]
  simp [D, Matrix.diagonal_pow, Matrix.trace_diagonal, ← Complex.ofReal_pow]

/-- An even trace moment dominates the corresponding power of the actual
operator norm, without a dimension factor for the unnormalized trace. -/
theorem norm_pow_le_trace_even [Nonempty ι] (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (p : ℕ) :
    ‖A‖ ^ (2 * p) ≤ (A ^ (2 * p)).trace.re := by
  classical
  letI : CStarAlgebra (Matrix ι ι ℂ) := { }
  let f : ι → ℂ := fun i => (hA.eigenvalues i : ℂ)
  have hn : ‖A‖ = ‖f‖ := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [StarAlgEquiv.norm_map, Matrix.l2_opNorm_diagonal]
    rfl
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖f i‖)
    Finset.univ_nonempty
  have hm : ‖f‖ = ‖f i‖ := le_antisymm
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun j => hi j (Finset.mem_univ _)))
    (norm_le_pi_norm f i)
  rw [hn, hm, trace_pow_re_eq_sum A hA]
  have he : ‖f i‖ ^ (2 * p) = hA.eigenvalues i ^ (2 * p) := by
    simp only [f, Complex.norm_real, Real.norm_eq_abs, pow_mul, sq_abs]
  rw [he]
  exact Finset.single_le_sum (f := fun j => hA.eigenvalues j ^ (2 * p))
    (fun j _ => by dsimp; rw [pow_mul]; positivity) (Finset.mem_univ i)











end Nonadditivity.HaarMomentTail


