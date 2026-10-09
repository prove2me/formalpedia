-- Prove2me | Definitions.Def_Nonadditivity_Entropy
-- name    : Nonadditivity_Entropy
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:19:09.317982+00:00
-- url     : https://prove2.me/theorems/e8a2f259-da6f-464c-9682-96fb2f5c457f
-- title:
--   Finite density matrices, von Neumann entropy, and purity
-- statement:
--   A density matrix on a finite index set is a positive semidefinite complex matrix of trace one. Its eigenvalues form a probability distribution, and its von Neumann entropy is their Shannon entropy with natural logarithms. This interface defines purity and the centered matrix, proves the bounds $-\log\operatorname{tr}(\rho^2)\le S(\rho)\le\log d$, and relates centered Hilbert–Schmidt bounds to purity. Unitary conjugation and complex conjugation preserve entropy; the Bell vector is invariant under the paired unitary action.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/Entropy.lean#L32-L385

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
# Entropy and purity components of `nonadditivity.tex`

The results in the first sections are unconditional statements about finite
probability distributions and complex positive semidefinite matrices. Entropies
use natural logarithms. Divide by `Real.log 2` to obtain the paper's convention.

The Bell weight computation proves the Shannon entropy of the actual list of
weights. It does not claim to prove the quantum mixture entropy inequality,
the complementary-output entropy identity, or the Weyl extension theorem.
-/

namespace Nonadditivity.Entropy

open scoped BigOperators ComplexOrder ComplexConjugate Kronecker Matrix

noncomputable section

def shannon {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  -∑ i, p i * Real.log (p i)

def distributionPurity {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, p i ^ 2

theorem distributionPurity_pos {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hsum : ∑ i, p i = 1) : 0 < distributionPurity p := by
  classical
  have hn : 0 ≤ distributionPurity p := Finset.sum_nonneg (fun i _ => sq_nonneg (p i))
  by_contra hp
  have hz : distributionPurity p = 0 := le_antisymm (le_of_not_gt hp) hn
  have hzero : ∀ i, p i = 0 := by
    intro i
    have hi : p i ^ 2 ≤ distributionPurity p := Finset.single_le_sum
      (fun j _ => sq_nonneg (p j)) (Finset.mem_univ i)
    nlinarith
  simp only [hzero, Finset.sum_const_zero] at hsum
  norm_num at hsum

/-- The order-two Rényi lower bound for a finite distribution, including zero weights. -/
theorem shannon_ge_neg_log_purity {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    -Real.log (distributionPurity p) ≤ shannon p := by
  classical
  let r := distributionPurity p
  have hr : 0 < r := distributionPurity_pos p hsum
  have hterm (i : ι) :
      p i * (Real.log (p i) - Real.log r) ≤ p i * (p i / r - 1) := by
    by_cases hz : p i = 0
    · simp [hz]
    · have hi : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hz)
      have hh := Real.log_le_sub_one_of_pos (div_pos hi hr)
      rw [Real.log_div hz (ne_of_gt hr)] at hh
      exact mul_le_mul_of_nonneg_left hh (hp i)
  have hsumterm := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  have hleft : (∑ i, p i * (Real.log (p i) - Real.log r)) =
      (∑ i, p i * Real.log (p i)) - Real.log r := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  have hright : (∑ i, p i * (p i / r - 1)) = 0 := by
    simp only [mul_sub, mul_one, ← mul_div_assoc, ← pow_two,
      Finset.sum_sub_distrib, ← Finset.sum_div, hsum]
    change r / r - 1 = 0
    simp [ne_of_gt hr]
  rw [hleft, hright] at hsumterm
  unfold shannon
  change -Real.log r ≤ _
  linarith

theorem shannon_nonneg {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) : 0 ≤ shannon p := by
  classical
  have hterm (i : ι) : p i * Real.log (p i) ≤ 0 := by
    by_cases hz : p i = 0
    · simp [hz]
    · have hi : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hz)
      have hle : p i ≤ 1 := by
        rw [← hsum]
        exact Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)
      exact mul_nonpos_of_nonneg_of_nonpos (hp i) (Real.log_nonpos (le_of_lt hi) hle)
  have hsumterm := Finset.sum_nonpos (fun i (_ : i ∈ Finset.univ) => hterm i)
  unfold shannon
  linarith

/-- The usual finite-alphabet entropy maximum, proved directly from `log x ≤ x-1`. -/
theorem shannon_le_log_card {ι : Type*} [Fintype ι] [Nonempty ι]
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    shannon p ≤ Real.log (Fintype.card ι) := by
  classical
  let d : ℝ := Fintype.card ι
  have hd : 0 < d := by
    change (0 : ℝ) < Fintype.card ι
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  have hterm (i : ι) : p i - 1 / d - p i * Real.log d ≤ p i * Real.log (p i) := by
    by_cases hz : p i = 0
    · simp only [hz, zero_sub, zero_mul, sub_zero]
      exact neg_nonpos.mpr (le_of_lt (div_pos zero_lt_one hd))
    · have hi : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hz)
      have hlog := Real.one_sub_inv_le_log_of_pos (mul_pos hd hi)
      rw [Real.log_mul (ne_of_gt hd) hz] at hlog
      have hm := mul_le_mul_of_nonneg_left hlog (hp i)
      have hfrac : p i * (1 - (d * p i)⁻¹) = p i - 1 / d := by
        field_simp
      rw [hfrac] at hm
      nlinarith
  have hsumterm := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  have hleft : (∑ i, (p i - 1 / d - p i * Real.log d)) = -Real.log d := by
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, one_mul]
    change 1 - d * (1 / d) - Real.log d = -Real.log d
    field_simp
    ring
  rw [hleft] at hsumterm
  unfold shannon
  change _ ≤ Real.log d
  linarith



/-! ## Actual finite quantum density matrices -/

/-- A finite-dimensional quantum density matrix. -/
structure DensityMatrix (ι : Type*) [Fintype ι] [DecidableEq ι] where
  matrix : Matrix ι ι ℂ
  positive : matrix.PosSemidef
  normalized : matrix.trace = 1

def DensityMatrix.weights {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : DensityMatrix ι) : ι → ℝ :=
  ρ.positive.isHermitian.eigenvalues

theorem DensityMatrix.weights_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : DensityMatrix ι) (i : ι) : 0 ≤ ρ.weights i :=
  ρ.positive.eigenvalues_nonneg i

theorem DensityMatrix.weights_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : DensityMatrix ι) : ∑ i, ρ.weights i = 1 := by
  have h := ρ.positive.isHermitian.trace_eq_sum_eigenvalues
  rw [ρ.normalized] at h
  have hre := congrArg Complex.re h
  simpa [DensityMatrix.weights] using hre.symm

/-- Von Neumann entropy defined spectrally, with the convention `0 log 0 = 0`. -/
def DensityMatrix.vonNeumann {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : DensityMatrix ι) : ℝ := shannon ρ.weights

/-- Spectral purity. The following theorem identifies it with the matrix trace. -/
def DensityMatrix.purity {ι : Type*} [Fintype ι] [DecidableEq ι]
  (ρ : DensityMatrix ι) : ℝ := distributionPurity ρ.weights

theorem DensityMatrix.purity_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : DensityMatrix ι) : 0 < ρ.purity :=
  distributionPurity_pos ρ.weights ρ.weights_sum

theorem DensityMatrix.trace_square_eq_purity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : DensityMatrix ι) : (ρ.matrix * ρ.matrix).trace = (ρ.purity : ℂ) := by
  let U := ρ.positive.isHermitian.eigenvectorUnitary
  let D := Matrix.diagonal (fun i => (ρ.weights i : ℂ))
  have hs : ρ.matrix = Unitary.conjStarAlgAut ℂ _ U D :=
    ρ.positive.isHermitian.spectral_theorem
  calc
    (ρ.matrix * ρ.matrix).trace =
        (Unitary.conjStarAlgAut ℂ _ U (D * D)).trace := by rw [map_mul, ← hs]
    _ = (D * D).trace := by
      rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, ← Matrix.mul_assoc,
        Unitary.coe_star_mul_self, Matrix.one_mul]
    _ = (ρ.purity : ℂ) := by
      simp [D, DensityMatrix.purity, distributionPurity, Matrix.diagonal_mul_diagonal,
        Matrix.trace_diagonal, pow_two]

/-- The actual von Neumann entropy versus order-two Rényi entropy inequality. -/
theorem DensityMatrix.vonNeumann_ge_neg_log_purity
    {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : DensityMatrix ι) :
    -Real.log ρ.purity ≤ ρ.vonNeumann :=
  shannon_ge_neg_log_purity ρ.weights ρ.weights_nonneg ρ.weights_sum

theorem DensityMatrix.vonNeumann_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : DensityMatrix ι) :
    0 ≤ ρ.vonNeumann :=
  shannon_nonneg ρ.weights ρ.weights_nonneg ρ.weights_sum

theorem DensityMatrix.vonNeumann_le_log_dim
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (ρ : DensityMatrix ι) :
    ρ.vonNeumann ≤ Real.log (Fintype.card ι) :=
  shannon_le_log_card ρ.weights ρ.weights_nonneg ρ.weights_sum

/-- Deviation from the maximally mixed output. -/
def DensityMatrix.centered {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : DensityMatrix ι) : Matrix ι ι ℂ :=
  ρ.matrix - (1 / (Fintype.card ι : ℂ)) • 1

theorem DensityMatrix.centered_isHermitian {ι : Type*} [Fintype ι]
    [DecidableEq ι] (ρ : DensityMatrix ι) : ρ.centered.IsHermitian := by
  simp [Matrix.IsHermitian, DensityMatrix.centered,
    ρ.positive.isHermitian.eq]

theorem DensityMatrix.centered_trace_zero {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (ρ : DensityMatrix ι) : ρ.centered.trace = 0 := by
  have hd : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [DensityMatrix.centered, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_one, ρ.normalized, hd]

/-- Trace pairing with the output equals the squared centered Hilbert--Schmidt length. -/
theorem DensityMatrix.centered_trace_pairing {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (ρ : DensityMatrix ι) :
    (ρ.centered * ρ.centered).trace = (ρ.matrix * ρ.centered).trace := by
  change ((ρ.matrix - (1 / (Fintype.card ι : ℂ)) • 1) * ρ.centered).trace = _
  simp [Matrix.sub_mul, Matrix.trace_sub,
    Matrix.trace_smul, ρ.centered_trace_zero]

/-- The exact centered-purity decomposition used in Lemma `purity`. -/
theorem DensityMatrix.centered_trace_square {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (ρ : DensityMatrix ι) :
    (ρ.centered * ρ.centered).trace =
      (ρ.purity : ℂ) - 1 / (Fintype.card ι : ℂ) := by
  have hd : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [DensityMatrix.centered, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.trace_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.trace_smul, ρ.normalized,
    Matrix.trace_one, ρ.trace_square_eq_purity, smul_eq_mul, mul_one]
  field_simp
  ring

theorem DensityMatrix.purity_eq_inv_dim_add_centered {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (ρ : DensityMatrix ι) :
    ρ.purity = 1 / (Fintype.card ι : ℝ) +
      (ρ.centered * ρ.centered).trace.re := by
  have h := congrArg Complex.re ρ.centered_trace_square
  simp only [Complex.sub_re, Complex.ofReal_re, ← Complex.ofReal_natCast,
    ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re] at h
  linarith

/-- A concrete entropy bound for a finite density matrix satisfying a purity certificate.
This is the final entropy step of Lemma `purity`, independent of how the
certificate is produced. -/
theorem DensityMatrix.entropy_bound_of_purity {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (ρ : DensityMatrix ι) (t : ℝ)
    (hpurity : ρ.purity ≤ 1 / (Fintype.card ι : ℝ) + t ^ 2) :
    Real.log (Fintype.card ι) - Real.log (1 + (Fintype.card ι : ℝ) * t ^ 2) ≤
      ρ.vonNeumann := by
  have hd : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  have hb : 0 < 1 / (Fintype.card ι : ℝ) + t ^ 2 :=
    add_pos_of_pos_of_nonneg (div_pos zero_lt_one hd) (sq_nonneg t)
  have hlog := Real.log_le_log ρ.purity_pos hpurity
  have hrearr : 1 / (Fintype.card ι : ℝ) + t ^ 2 =
      (1 + (Fintype.card ι : ℝ) * t ^ 2) / (Fintype.card ι : ℝ) := by
    field_simp
  have htpos : 0 < 1 + (Fintype.card ι : ℝ) * t ^ 2 := by
    nlinarith [mul_nonneg (le_of_lt hd) (sq_nonneg t)]
  rw [hrearr, Real.log_div (ne_of_gt htpos) (ne_of_gt hd)] at hlog
  have hrenyi := ρ.vonNeumann_ge_neg_log_purity
  linarith

/-- The centered Hilbert--Schmidt certificate implies both claims of Lemma `purity`. -/
theorem DensityMatrix.purity_and_entropy_of_centered_bound {ι : Type*} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] (ρ : DensityMatrix ι) (t : ℝ)
    (hcenter : (ρ.centered * ρ.centered).trace.re ≤ t ^ 2) :
    ρ.purity ≤ 1 / (Fintype.card ι : ℝ) + t ^ 2 ∧
    Real.log (Fintype.card ι) - Real.log (1 + (Fintype.card ι : ℝ) * t ^ 2) ≤
      ρ.vonNeumann := by
  have hp : ρ.purity ≤ 1 / (Fintype.card ι : ℝ) + t ^ 2 := by
    rw [ρ.purity_eq_inv_dim_add_centered]
    linarith
  exact ⟨hp, ρ.entropy_bound_of_purity t hp⟩

/-- Conjugation of a genuine density matrix by a genuine unitary matrix. -/
def DensityMatrix.unitaryConjugate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : DensityMatrix ι) (U : unitary (Matrix ι ι ℂ)) : DensityMatrix ι where
  matrix := (U : Matrix ι ι ℂ) * ρ.matrix * (star U : Matrix ι ι ℂ)
  positive := ρ.positive.mul_mul_conjTranspose_same (U : Matrix ι ι ℂ)
  normalized := by
    rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul]
    exact ρ.normalized

theorem DensityMatrix.unitaryConjugate_weights {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : DensityMatrix ι) (U : unitary (Matrix ι ι ℂ)) :
    (ρ.unitaryConjugate U).weights = ρ.weights := by
  apply ((ρ.unitaryConjugate U).positive.isHermitian.eigenvalues_eq_eigenvalues_iff
    ρ.positive.isHermitian).mpr
  change (U * ρ.matrix * (star U : Matrix ι ι ℂ)).charpoly = ρ.matrix.charpoly
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, Unitary.coe_star_mul_self,
    Matrix.one_mul]

/-- Unitary invariance of actual von Neumann entropy. -/
theorem DensityMatrix.unitaryConjugate_entropy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : DensityMatrix ι) (U : unitary (Matrix ι ι ℂ)) :
    (ρ.unitaryConjugate U).vonNeumann = ρ.vonNeumann := by
  simp only [DensityMatrix.vonNeumann, ρ.unitaryConjugate_weights U]

/-- Entrywise conjugation of a Hermitian density matrix equals its transpose. -/
def DensityMatrix.conjugate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : DensityMatrix ι) : DensityMatrix ι where
  matrix := ρ.matrix.transpose
  positive := ρ.positive.transpose
  normalized := by simpa using ρ.normalized

theorem DensityMatrix.conjugate_weights {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : DensityMatrix ι) : ρ.conjugate.weights = ρ.weights := by
  apply (ρ.conjugate.positive.isHermitian.eigenvalues_eq_eigenvalues_iff
    ρ.positive.isHermitian).mpr
  exact Matrix.charpoly_transpose ρ.matrix

/-- Entropy equality of conjugate quantum output states. -/
theorem DensityMatrix.conjugate_entropy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : DensityMatrix ι) : ρ.conjugate.vonNeumann = ρ.vonNeumann := by
  simp only [DensityMatrix.vonNeumann, ρ.conjugate_weights]

/-! ## Bell-mixture weights (the classical component of Lemma `bell`) -/









/-! ## The actual Bell-vector unitary identity -/

/-- The unnormalized Bell vector in the product basis. -/
def bellVector {ι : Type*} [DecidableEq ι] : ι × ι → ℂ :=
  fun ij => if ij.1 = ij.2 then 1 else 0

/-- `U ⊗ conjugate(U)` fixes the Bell vector, for any finite-dimensional unitary. -/
theorem unitary_kronecker_conjugate_fixes_bell {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) :
    ((U : Matrix ι ι ℂ) ⊗ₖ (U : Matrix ι ι ℂ).map (starRingEnd ℂ)) *ᵥ
      (bellVector : ι × ι → ℂ) = bellVector := by
  ext ⟨i, j⟩
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kronecker_apply,
    Matrix.map_apply, bellVector, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have h := congrArg (fun M : Matrix ι ι ℂ => M i j) (Unitary.coe_mul_star_self U)
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h

/-- The same identity for any scalar normalization, including `1 / sqrt(dim)`. -/
theorem unitary_kronecker_conjugate_fixes_scaled_bell
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) (c : ℂ) :
    ((U : Matrix ι ι ℂ) ⊗ₖ (U : Matrix ι ι ℂ).map (starRingEnd ℂ)) *ᵥ
      (c • (bellVector : ι × ι → ℂ)) = c • bellVector := by
  rw [Matrix.mulVec_smul, unitary_kronecker_conjugate_fixes_bell]

end

end Nonadditivity.Entropy


