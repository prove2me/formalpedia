-- Prove2me | Definitions.Def_Nonadditivity_EntropyContinuity
-- name    : Nonadditivity_EntropyContinuity
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:45:52.694318+00:00
-- url     : https://prove2.me/theorems/d9999447-e512-4f65-be96-badd30efc180
-- title:
--   Uniform entropy continuity in fixed finite dimension
-- statement:
--   On a fixed finite complex matrix index set $I$, let $S(\rho)$ be the spectral von Neumann entropy of a density matrix $\rho$, in the library's natural-logarithm convention. For every $\eta>0$, there is a $\delta>0$ such that
--   $$\|\rho-\sigma\|\le\delta\ \Longrightarrow\ |S(\rho)-S(\sigma)|\le\eta$$
--   for all density matrices on $I$. For nonempty $I$, the same conclusion holds with Hilbert–Schmidt distance in place of Euclidean operator norm. The bundle also supplies a uniform Shannon-entropy modulus for finite coordinate vectors in $[0,1]$, including zero coordinates; bounds diagonal expectations of a Hermitian matrix by its operator norm; and proves that unitary conjugation preserves the norm of a difference. These fixed-dimension continuity tools control entropy errors introduced by finite realization and damping.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/EntropyContinuity.lean#L30-L147

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
import Definitions.Def_Nonadditivity_HaarMomentTail
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
import Mathlib.Topology.UniformSpace.HeineCantor

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/




/-!
# Uniform continuity of finite-dimensional von Neumann entropy

The modulus depends only on the output dimension and the requested entropy
error.  It is obtained from scalar uniform continuity on `[0,1]`, diagonal
pinching, and unitary invariance, without any assumed spectral continuity
or probabilistic estimate.
-/

noncomputable section

namespace Nonadditivity.EntropyContinuity

open Nonadditivity.Entropy Nonadditivity.EntropyMixtures
open scoped BigOperators ComplexOrder Matrix MatrixOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A uniform scalar modulus gives a uniform modulus for finite Shannon
entropy, including boundary distributions with zero probabilities. -/
theorem exists_shannon_modulus (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ p q : ι → ℝ,
      (∀ i, p i ∈ Set.Icc (0 : ℝ) 1) →
      (∀ i, q i ∈ Set.Icc (0 : ℝ) 1) →
      (∀ i, |p i - q i| ≤ δ) → |shannon p - shannon q| ≤ η := by
  classical
  have hd : 0 < (Fintype.card ι : ℝ) + 1 := by positivity
  have hu := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).uniformContinuousOn_of_continuous
    Real.continuous_negMulLog.continuousOn
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff_le.mp hu
    (η / ((Fintype.card ι : ℝ) + 1)) (div_pos hη hd)
  refine ⟨δ, hδ, fun p q hp hq hpq => ?_⟩
  rw [shannon_eq_sum_negMulLog, shannon_eq_sum_negMulLog, ← Finset.sum_sub_distrib]
  calc
    |∑ i, (Real.negMulLog (p i) - Real.negMulLog (q i))| ≤
        ∑ i, |Real.negMulLog (p i) - Real.negMulLog (q i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, η / ((Fintype.card ι : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro i _
      exact hmod (p i) (hp i) (q i) (hq i) (by simpa [Real.dist_eq] using hpq i)
    _ ≤ η := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hd).mpr
      nlinarith

lemma diagonal_mem_Icc (ρ : DensityMatrix ι) (i : ι) :
    (ρ.matrix i i).re ∈ Set.Icc (0 : ℝ) 1 := by
  have hn (j : ι) : 0 ≤ (ρ.matrix j j).re :=
    (Complex.nonneg_iff.mp ρ.positive.diag_nonneg).1
  have hs : (∑ j, (ρ.matrix j j).re) = 1 := by
    simpa only [Matrix.trace, ← Complex.re_sum, Complex.one_re] using
      congrArg Complex.re ρ.normalized
  exact ⟨hn i, hs ▸ Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)⟩

/-- Diagonal expectations of a Hermitian matrix are bounded by its genuine
Euclidean operator norm. -/
lemma abs_diagonal_re_le_opNorm (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (i : ι) :
    |(A i i).re| ≤ ‖A‖ := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := { }
  have hu : A ≤ algebraMap ℝ (Matrix ι ι ℂ) ‖A‖ :=
    IsSelfAdjoint.le_algebraMap_norm_self hA.isSelfAdjoint
  have hl : -A ≤ algebraMap ℝ (Matrix ι ι ℂ) ‖-A‖ :=
    IsSelfAdjoint.le_algebraMap_norm_self hA.neg.isSelfAdjoint
  have hu' : 0 ≤ ((algebraMap ℝ (Matrix ι ι ℂ) ‖A‖ - A) i i).re :=
    (Complex.nonneg_iff.mp (Matrix.le_iff.mp hu).diag_nonneg).1
  have hl' : 0 ≤ ((algebraMap ℝ (Matrix ι ι ℂ) ‖-A‖ - -A) i i).re :=
    (Complex.nonneg_iff.mp (Matrix.le_iff.mp hl).diag_nonneg).1
  simp [Algebra.algebraMap_eq_smul_one, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.neg_apply] at hu' hl'
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma unitaryConjugate_sub_norm (ρ σ : DensityMatrix ι)
    (U : unitary (Matrix ι ι ℂ)) :
    ‖(ρ.unitaryConjugate U).matrix - (σ.unitaryConjugate U).matrix‖ =
      ‖ρ.matrix - σ.matrix‖ := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := { }
  change ‖(U : Matrix ι ι ℂ) * ρ.matrix * (star U : Matrix ι ι ℂ) -
    (U : Matrix ι ι ℂ) * σ.matrix * (star U : Matrix ι ι ℂ)‖ = _
  rw [← sub_mul, ← mul_sub]
  exact (CStarRing.norm_mul_coe_unitary _ (star U)).trans
    (CStarRing.norm_coe_unitary_mul U _)

/-- Uniform continuity in Euclidean operator norm of the actual spectral
von Neumann entropy on finite density matrices. -/
theorem exists_vonNeumann_opNorm_modulus (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ ρ σ : DensityMatrix ι,
      ‖ρ.matrix - σ.matrix‖ ≤ δ → |ρ.vonNeumann - σ.vonNeumann| ≤ η := by
  obtain ⟨δ, hδ, hmod⟩ := exists_shannon_modulus (ι := ι) η hη
  have hone (ρ σ : DensityMatrix ι) (hclose : ‖ρ.matrix - σ.matrix‖ ≤ δ) :
      ρ.vonNeumann ≤ σ.vonNeumann + η := by
    let U := star σ.positive.isHermitian.eigenvectorUnitary
    let τ := ρ.unitaryConjugate U
    let ω := σ.unitaryConjugate U
    have hdiag : ω.matrix = Matrix.diagonal (fun i => (σ.weights i : ℂ)) :=
      σ.positive.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
    have hcoord (i : ι) : |(τ.matrix i i).re - (ω.matrix i i).re| ≤ δ := by
      calc
        |(τ.matrix i i).re - (ω.matrix i i).re| = |((τ.matrix - ω.matrix) i i).re| := rfl
        _ ≤ ‖τ.matrix - ω.matrix‖ := abs_diagonal_re_le_opNorm _
          (τ.positive.isHermitian.sub ω.positive.isHermitian) i
        _ = ‖ρ.matrix - σ.matrix‖ := unitaryConjugate_sub_norm ρ σ U
        _ ≤ δ := hclose
    have hs := hmod (fun i => (τ.matrix i i).re) (fun i => (ω.matrix i i).re)
      (diagonal_mem_Icc τ) (diagonal_mem_Icc ω) hcoord
    have hspec : shannon (fun i => (ω.matrix i i).re) = σ.vonNeumann := by
      simp only [hdiag, Matrix.diagonal_apply_eq, Complex.ofReal_re]
      rfl
    rw [hspec] at hs
    have hp := DensityMatrix.vonNeumann_le_diagonal τ
    have he : τ.vonNeumann = ρ.vonNeumann := ρ.unitaryConjugate_entropy U
    have hh := (abs_le.mp hs).2
    linarith
  refine ⟨δ, hδ, fun ρ σ hclose => abs_le.mpr ⟨?_, ?_⟩⟩
  · have hrev : ‖σ.matrix - ρ.matrix‖ ≤ δ := by
      simpa only [norm_sub_rev] using hclose
    linarith [hone σ ρ hrev]
  · linarith [hone ρ σ hclose]

/-- The same uniform modulus applies to Hilbert--Schmidt perturbations. -/
theorem exists_vonNeumann_hsLength_modulus [Nonempty ι] (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ ρ σ : DensityMatrix ι,
      AdjointPurity.hsLength (ρ.matrix - σ.matrix) ≤ δ →
        |ρ.vonNeumann - σ.vonNeumann| ≤ η := by
  obtain ⟨δ, hδ, hmod⟩ := exists_vonNeumann_opNorm_modulus (ι := ι) η hη
  refine ⟨δ, hδ, fun ρ σ hclose => hmod ρ σ ?_⟩
  have hHerm := ρ.positive.isHermitian.sub σ.positive.isHermitian
  have hnorm := HaarMomentTail.norm_pow_le_trace_even (ρ.matrix - σ.matrix) hHerm 1
  simp only [show 2 * 1 = 2 by omega, pow_two] at hnorm
  have hs := AdjointPurity.hsLength_sq_of_isHermitian (ρ.matrix - σ.matrix) hHerm
  have hn : ‖ρ.matrix - σ.matrix‖ ≤ AdjointPurity.hsLength (ρ.matrix - σ.matrix) := by
    nlinarith [norm_nonneg (ρ.matrix - σ.matrix),
      AdjointPurity.hsLength_nonneg (ρ.matrix - σ.matrix)]
  exact hn.trans hclose

end Nonadditivity.EntropyContinuity


