-- Prove2me | Definitions.Def_Nonadditivity_PureChannelEntropy
-- name    : Nonadditivity_PureChannelEntropy
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:33:14.772427+00:00
-- url     : https://prove2.me/theorems/9668ada7-e092-471a-aff8-ae158375ba81
-- title:
--   Pure input states and complementary-channel entropy equality
-- statement:
--   A normalized vector defines a rank-one density matrix of zero entropy. For such an input to a finite Kraus channel, the output and complementary output are the two Gram states of the same coefficient matrix. Their von Neumann entropies are consequently equal. The construction includes the normalization and matrix identities needed to apply this equality to explicit pure states.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/PureChannelEntropy.lean#L24-L119

import Definitions.Def_Nonadditivity_Channels
import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_EntropyProducts
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/




/-!
# Entropy equality of channel and complementary outputs for pure inputs

The coefficient matrix is constructed explicitly from the actual Kraus
operators. The two output matrices are identified with its two Gram matrices;
the entropy equality then follows from the proved rectangular spectral theorem.
-/

namespace Nonadditivity.Channels

open Nonadditivity.Entropy
open scoped BigOperators ComplexOrder ComplexConjugate Kronecker Matrix

noncomputable section

theorem densityMatrix_ext {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ σ : DensityMatrix ι) (h : ρ.matrix = σ.matrix) : ρ = σ := by
  cases ρ with
  | mk A hA htrA =>
    cases σ with
    | mk B hB htrB =>
      change A = B at h
      subst B
      rfl

/-- The actual rank-one input density matrix of a normalized finite vector. -/
def pureState {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℂ) (hv : ∑ i, Complex.normSq (v i) = 1) : DensityMatrix ι where
  matrix := Matrix.vecMulVec v (star v)
  positive := Matrix.posSemidef_vecMulVec_self_star v
  normalized := by
    have h : ∑ i, (Complex.normSq (v i) : ℂ) = 1 := by exact_mod_cast hv
    change (∑ i, v i * star (v i)) = 1
    have hterm (i : ι) : v i * star (v i) = (Complex.normSq (v i) : ℂ) :=
      Complex.mul_conj (v i)
    simp_rw [hterm]
    exact h

/-- Every actual normalized rank-one density matrix has zero von Neumann entropy. -/
theorem pureState_entropy_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℂ) (hv : ∑ i, Complex.normSq (v i) = 1) :
    (pureState v hv).vonNeumann = 0 := by
  let A : Matrix ι Unit ℂ := fun i _ => v i
  have hA : (pureState v hv).matrix = A * Aᴴ := by
    ext i j
    simp [pureState, A, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.vecMulVec_apply, Pi.star_apply]
  have hn : (A * Aᴴ).trace = 1 := by
    rw [← hA]
    exact (pureState v hv).normalized
  have hs : pureState v hv = bipartiteLeft A hn :=
    densityMatrix_ext _ _ hA
  rw [hs, bipartite_entropy_eq]
  apply le_antisymm
  · simpa using (bipartiteRight A hn).vonNeumann_le_log_dim
  · exact (bipartiteRight A hn).vonNeumann_nonneg

namespace KrausChannel

variable {ι ο κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype ο] [DecidableEq ο] [Fintype κ] [DecidableEq κ]

/-- Pure Stinespring output as an output-by-environment coefficient matrix. -/
def pureCoefficients (T : KrausChannel ι ο κ) (v : ι → ℂ) : Matrix ο κ ℂ :=
  fun b e => (T.kraus e *ᵥ v) b

omit [DecidableEq ο] [DecidableEq κ] in
/-- The system output is the left Gram matrix of the explicit Stinespring coefficients. -/
theorem map_rankOne_eq_gram (T : KrausChannel ι ο κ) (v : ι → ℂ) :
    T.map (Matrix.vecMulVec v (star v)) =
      T.pureCoefficients v * (T.pureCoefficients v)ᴴ := by
  simp only [map, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  ext b c
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, pureCoefficients,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.vecMul, Matrix.mulVec,
    dotProduct, Pi.star_apply, star_sum, star_mul]

omit [DecidableEq ο] [DecidableEq κ] in
/-- The environment output is the transpose of the right Gram matrix. -/
theorem complementary_map_rankOne_eq_gram (T : KrausChannel ι ο κ) (v : ι → ℂ) :
    T.complementary.map (Matrix.vecMulVec v (star v)) =
      ((T.pureCoefficients v)ᴴ * T.pureCoefficients v).transpose := by
  rw [T.complementary.map_rankOne_eq_gram]
  ext e f
  simp [pureCoefficients, complementary, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.mulVec, dotProduct, mul_comm]

omit [DecidableEq ο] [DecidableEq κ] in
/-- Kraus completeness and input normalization imply normalization of the coefficient matrix. -/
theorem pureCoefficients_normalized (T : KrausChannel ι ο κ) (v : ι → ℂ)
    (hv : ∑ i, Complex.normSq (v i) = 1) :
    (T.pureCoefficients v * (T.pureCoefficients v)ᴴ).trace = 1 := by
  rw [← T.map_rankOne_eq_gram v, T.trace_map]
  exact (pureState v hv).normalized

/-- Actual pure-input channel/complement entropy equality; no Schmidt equality is assumed. -/
theorem pure_output_complementary_entropy_eq (T : KrausChannel ι ο κ) (v : ι → ℂ)
    (hv : ∑ i, Complex.normSq (v i) = 1) :
    (T.output (pureState v hv)).vonNeumann =
      (T.complementary.output (pureState v hv)).vonNeumann := by
  let A := T.pureCoefficients v
  let hn := T.pureCoefficients_normalized v hv
  have hleft : T.output (pureState v hv) = bipartiteLeft A hn := by
    apply densityMatrix_ext
    exact T.map_rankOne_eq_gram v
  have hright : T.complementary.output (pureState v hv) =
      (bipartiteRight A hn).conjugate := by
    apply densityMatrix_ext
    exact T.complementary_map_rankOne_eq_gram v
  rw [hleft, hright]
  exact bipartite_physical_reductions_entropy_eq A hn

end KrausChannel

end

end Nonadditivity.Channels


