-- Prove2me | Definitions.Def_Nonadditivity_EntropyProducts
-- name    : Nonadditivity_EntropyProducts
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:22:00.818378+00:00
-- url     : https://prove2.me/theorems/e82d1630-e4a1-4c42-ab77-a5ee380fc78a
-- title:
--   Entropy of tensor products and bipartite Gram states
-- statement:
--   Tensoring finite density matrices produces a density matrix whose von Neumann entropy is the sum of the two entropies. The proof identifies its spectral weights with products of the original weights and uses additivity of Shannon entropy. The interface also constructs the normalized left and right Gram states of a coefficient matrix and proves that their entropies agree, including the zero eigenvalues introduced by differing dimensions. Entropies use natural logarithms.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/EntropyProducts.lean#L24-L185

import Definitions.Def_Nonadditivity_Entropy
import Mathlib.Analysis.Matrix.Order
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
# Tensor products of actual quantum density matrices

This file constructs the Kronecker product of two PSD trace-one complex
matrices and proves von Neumann entropy additivity. No entropy law or
eigenvalue formula is postulated: the proof uses unitary diagonalization,
characteristic-polynomial root multisets, and the logarithm product identity.
-/

namespace Nonadditivity.Entropy

open scoped BigOperators ComplexOrder ComplexConjugate Kronecker Matrix

noncomputable section

theorem mul_log_mul (x y : ℝ) :
    (x * y) * Real.log (x * y) = (x * Real.log x) * y + x * (y * Real.log y) := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  rw [Real.log_mul hx hy]
  ring

/-- Shannon entropy is additive for product distributions, including zero weights. -/
theorem shannon_product {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (q : κ → ℝ) (hp : ∑ i, p i = 1) (hq : ∑ j, q j = 1) :
    shannon (fun ij : ι × κ => p ij.1 * q ij.2) = shannon p + shannon q := by
  simp only [shannon, Fintype.sum_prod_type, mul_log_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, hp, hq, mul_one, one_mul]
  ring

/-- The genuine tensor-product density matrix. -/
def DensityMatrix.tensor {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (ρ : DensityMatrix ι) (σ : DensityMatrix κ) :
    DensityMatrix (ι × κ) where
  matrix := ρ.matrix ⊗ₖ σ.matrix
  positive := ρ.positive.kronecker σ.positive
  normalized := by rw [Matrix.trace_kronecker, ρ.normalized, σ.normalized, one_mul]

theorem DensityMatrix.tensor_matrix {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (ρ : DensityMatrix ι) (σ : DensityMatrix κ) :
    (ρ.tensor σ).matrix = ρ.matrix ⊗ₖ σ.matrix := rfl

/-- Tensoring actual unitaries gives an actual unitary. -/
def tensorUnitary {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (U : unitary (Matrix ι ι ℂ)) (V : unitary (Matrix κ κ ℂ)) :
    unitary (Matrix (ι × κ) (ι × κ) ℂ) :=
  ⟨(U : Matrix ι ι ℂ) ⊗ₖ (V : Matrix κ κ ℂ), by
    rw [Unitary.mem_iff]
    constructor
    · change ((U : Matrix ι ι ℂ) ⊗ₖ (V : Matrix κ κ ℂ))ᴴ *
        ((U : Matrix ι ι ℂ) ⊗ₖ (V : Matrix κ κ ℂ)) = 1
      rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
      simp only [← Matrix.star_eq_conjTranspose, Unitary.coe_star_mul_self]
      exact Matrix.one_kronecker_one (m := ι) (n := κ)
    · change ((U : Matrix ι ι ℂ) ⊗ₖ (V : Matrix κ κ ℂ)) *
        ((U : Matrix ι ι ℂ) ⊗ₖ (V : Matrix κ κ ℂ))ᴴ = 1
      rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
      simp only [← Matrix.star_eq_conjTranspose]
      have hU : (U : Matrix ι ι ℂ) * star (U : Matrix ι ι ℂ) = 1 := by
        simpa only [Unitary.coe_star] using Unitary.coe_mul_star_self U
      have hV : (V : Matrix κ κ ℂ) * star (V : Matrix κ κ ℂ) = 1 := by
        simpa only [Unitary.coe_star] using Unitary.coe_mul_star_self V
      rw [hU, hV]
      exact Matrix.one_kronecker_one (m := ι) (n := κ)⟩

/-- Entropy can be evaluated using any unitary diagonalization, without sorting the eigenvalues. -/
theorem DensityMatrix.entropy_eq_shannon_of_diagonalization
    {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : DensityMatrix ι)
    (p : ι → ℝ) (U : unitary (Matrix ι ι ℂ))
    (h : ρ.matrix = (U : Matrix ι ι ℂ) * Matrix.diagonal (fun i => (p i : ℂ)) *
      (star U : Matrix ι ι ℂ)) : ρ.vonNeumann = shannon p := by
  have hc : ρ.matrix.charpoly = (Matrix.diagonal (fun i => (p i : ℂ))).charpoly := by
    rw [h, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
      Unitary.coe_star_mul_self, Matrix.one_mul]
  have hr : ρ.matrix.charpoly.roots =
      Multiset.map (fun i => (p i : ℂ)) Finset.univ.val := by
    rw [hc, Matrix.charpoly_diagonal, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have he := ρ.positive.isHermitian.roots_charpoly_eq_eigenvalues
  rw [hr] at he
  have hs := congrArg (fun s : Multiset ℂ =>
    (s.map (fun z => z.re * Real.log z.re)).sum) he
  simp only [Multiset.map_map, Function.comp_def, Complex.ofReal_re] at hs
  change (∑ i, p i * Real.log (p i)) =
    ∑ i, ρ.weights i * Real.log (ρ.weights i) at hs
  exact congrArg Neg.neg hs.symm

set_option maxHeartbeats 1000000 in
/-- The quantum entropy additivity law used for Bell output tensor blocks. -/
theorem DensityMatrix.tensor_entropy {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (ρ : DensityMatrix ι) (σ : DensityMatrix κ) :
    (ρ.tensor σ).vonNeumann = ρ.vonNeumann + σ.vonNeumann := by
  let U := ρ.positive.isHermitian.eigenvectorUnitary
  let V := σ.positive.isHermitian.eigenvectorUnitary
  have hρ : ρ.matrix = (U : Matrix ι ι ℂ) *
      Matrix.diagonal (fun i => (ρ.weights i : ℂ)) * (star U : Matrix ι ι ℂ) :=
    ρ.positive.isHermitian.spectral_theorem
  have hσ : σ.matrix = (V : Matrix κ κ ℂ) *
      Matrix.diagonal (fun j => (σ.weights j : ℂ)) * (star V : Matrix κ κ ℂ) :=
    σ.positive.isHermitian.spectral_theorem
  have ht : (ρ.tensor σ).matrix = (tensorUnitary U V : Matrix _ _ ℂ) *
      Matrix.diagonal (fun ij : ι × κ => ((ρ.weights ij.1 * σ.weights ij.2 : ℝ) : ℂ)) *
      (star (tensorUnitary U V) : Matrix _ _ ℂ) := by
    rw [DensityMatrix.tensor_matrix, hρ, hσ,
      Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul,
      Matrix.diagonal_kronecker_diagonal]
    simp only [tensorUnitary, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_kronecker, Complex.ofReal_mul]
  have he := (ρ.tensor σ).entropy_eq_shannon_of_diagonalization
    (fun ij : ι × κ => ρ.weights ij.1 * σ.weights ij.2) (tensorUnitary U V) ht
  exact he.trans (shannon_product ρ.weights σ.weights ρ.weights_sum σ.weights_sum)

/-! ## Rectangular Gram matrices and pure-state reductions -/

/-- The spectral entropy can equally be evaluated from characteristic-polynomial roots. -/
theorem DensityMatrix.entropy_eq_neg_root_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : DensityMatrix ι) :
    ρ.vonNeumann =
      -(ρ.matrix.charpoly.roots.map (fun z : ℂ => z.re * Real.log z.re)).sum := by
  rw [ρ.positive.isHermitian.roots_charpoly_eq_eigenvalues]
  simp only [Multiset.map_map, Function.comp_def]
  rfl

/-- Adding arbitrary zero eigenvalues leaves entropy unchanged.
The polynomial identity is an algebraic relation, not an entropy hypothesis. -/
theorem DensityMatrix.entropy_eq_of_padded_charpoly
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (ρ : DensityMatrix ι) (σ : DensityMatrix κ) (m n : ℕ)
    (h : (Polynomial.X : Polynomial ℂ) ^ m * ρ.matrix.charpoly =
      (Polynomial.X : Polynomial ℂ) ^ n * σ.matrix.charpoly) :
    ρ.vonNeumann = σ.vonNeumann := by
  have hr := congrArg Polynomial.roots h
  rw [Polynomial.roots_mul (mul_ne_zero
      (pow_ne_zero m Polynomial.X_ne_zero) ρ.matrix.charpoly_monic.ne_zero),
    Polynomial.roots_mul (mul_ne_zero
      (pow_ne_zero n Polynomial.X_ne_zero) σ.matrix.charpoly_monic.ne_zero),
    Polynomial.roots_X_pow, Polynomial.roots_X_pow] at hr
  have hs := congrArg (fun s : Multiset ℂ =>
    (s.map (fun z => z.re * Real.log z.re)).sum) hr
  simp [Multiset.nsmul_singleton, Multiset.map_replicate] at hs
  rw [ρ.entropy_eq_neg_root_sum, σ.entropy_eq_neg_root_sum]
  exact congrArg Neg.neg hs

/-- Left reduced state of a normalized bipartite pure vector represented as a coefficient matrix. -/
def bipartiteLeft {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (hnorm : (A * Aᴴ).trace = 1) : DensityMatrix ι where
  matrix := A * Aᴴ
  positive := Matrix.posSemidef_self_mul_conjTranspose A
  normalized := hnorm

/-- Right Gram state. Its transpose is the right physical reduction under
the coefficient convention; entropy is invariant under that conjugation. -/
def bipartiteRight {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (hnorm : (A * Aᴴ).trace = 1) : DensityMatrix κ where
  matrix := Aᴴ * A
  positive := Matrix.posSemidef_conjTranspose_mul_self A
  normalized := by rw [Matrix.trace_mul_comm]; exact hnorm

/-- Schmidt entropy equality, including unequal dimensions and zero Schmidt coefficients. -/
theorem bipartite_entropy_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℂ)
    (hnorm : (A * Aᴴ).trace = 1) :
    (bipartiteLeft A hnorm).vonNeumann = (bipartiteRight A hnorm).vonNeumann := by
  apply DensityMatrix.entropy_eq_of_padded_charpoly _ _ (Fintype.card κ) (Fintype.card ι)
  exact Matrix.charpoly_mul_comm' A Aᴴ

/-- Entropy equality for the actual coefficient-basis left and right reduced matrices. -/
theorem bipartite_physical_reductions_entropy_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℂ)
    (hnorm : (A * Aᴴ).trace = 1) :
    (bipartiteLeft A hnorm).vonNeumann = (bipartiteRight A hnorm).conjugate.vonNeumann := by
  rw [DensityMatrix.conjugate_entropy]
  exact bipartite_entropy_eq A hnorm

end

end Nonadditivity.Entropy


