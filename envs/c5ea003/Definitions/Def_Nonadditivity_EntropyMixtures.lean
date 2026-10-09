-- Prove2me | Definitions.Def_Nonadditivity_EntropyMixtures
-- name    : Nonadditivity_EntropyMixtures
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:32:52.67191+00:00
-- url     : https://prove2.me/theorems/d146a876-79e9-4b5e-8dc4-07d97b67746c
-- title:
--   Concavity and the entropy upper bound for finite mixtures
-- statement:
--   For a normalized finite mixture $\rho=\sum_i p_i\rho_i$, von Neumann entropy obeys $\sum_i p_iS(\rho_i)\le S(\rho)\le H(p)+\sum_i p_iS(\rho_i)$. The interface develops the ensemble coefficient matrix and its Gram states used to prove these inequalities. It also proves that entropy is bounded by the Shannon entropy of a matrix diagonal and that doubly stochastic averaging cannot decrease Shannon entropy. All entropies use natural logarithms.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/EntropyMixtures.lean#L27-L278

import Definitions.Def_Nonadditivity_Entropy
import Definitions.Def_Nonadditivity_EntropyProducts
import Definitions.Def_Nonadditivity_StateEnsembles
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/






/-!
# Entropy monotonicity under diagonal pinching

These statements concern genuine finite complex density matrices and their
spectrally defined von Neumann entropy. The pinching inequality is derived
from the spectral theorem, unitarity, and scalar Jensen's inequality; it is
not supplied as a hypothesis.
-/

namespace Nonadditivity.EntropyMixtures

open scoped BigOperators ComplexOrder ComplexConjugate Matrix
open Nonadditivity.Entropy

noncomputable section

lemma shannon_eq_sum_negMulLog {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    shannon p = ∑ i, Real.negMulLog (p i) := by
  simp [shannon, Real.negMulLog, Finset.sum_neg_distrib]

/-- A doubly stochastic matrix increases Shannon entropy, including zero
weights. This result is independent of a quantum interpretation. -/
theorem shannon_le_of_doublyStochastic {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : κ → ℝ) (hp : ∀ j, 0 ≤ p j) (q : ι → κ → ℝ)
    (hq : ∀ i j, 0 ≤ q i j) (hrow : ∀ i, ∑ j, q i j = 1)
    (hcol : ∀ j, ∑ i, q i j = 1) :
    shannon p ≤ shannon (fun i => ∑ j, q i j * p j) := by
  classical
  have hj (i : ι) :
      (∑ j, q i j * Real.negMulLog (p j)) ≤ Real.negMulLog (∑ j, q i j * p j) := by
    simpa only [smul_eq_mul] using Real.concaveOn_negMulLog.le_map_sum
      (t := Finset.univ) (w := q i) (p := p)
      (fun j _ => hq i j) (hrow i) (fun j _ => hp j)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hj i)
  have hleft : (∑ i, ∑ j, q i j * Real.negMulLog (p j)) =
      ∑ j, Real.negMulLog (p j) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, hcol, one_mul]
  rw [hleft] at hs
  simpa only [shannon_eq_sum_negMulLog] using hs

/-- Shannon entropy is concave for finite nonnegative distributions. -/
theorem shannon_mixture_concave {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : κ → ℝ) (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1)
    (q : κ → ι → ℝ) (hq : ∀ j i, 0 ≤ q j i) :
    (∑ j, p j * shannon (q j)) ≤ shannon (fun i => ∑ j, p j * q j i) := by
  classical
  have hj (i : ι) :
      (∑ j, p j * Real.negMulLog (q j i)) ≤ Real.negMulLog (∑ j, p j * q j i) := by
    simpa only [smul_eq_mul] using Real.concaveOn_negMulLog.le_map_sum
      (t := Finset.univ) (w := p) (p := fun j => q j i)
      (fun j _ => hp j) hsum (fun j _ => hq j i)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hj i)
  rw [Finset.sum_comm] at hs
  simpa only [shannon_eq_sum_negMulLog, Finset.mul_sum] using hs

/-- Squared matrix-entry moduli of a genuine unitary. -/
def unitaryWeights {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) (i j : ι) : ℝ :=
  Complex.normSq ((U : Matrix ι ι ℂ) i j)

lemma unitaryWeights_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) (i j : ι) : 0 ≤ unitaryWeights U i j :=
  Complex.normSq_nonneg _

lemma unitaryWeights_row_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) (i : ι) : ∑ j, unitaryWeights U i j = 1 := by
  have h := congrArg (fun M : Matrix ι ι ℂ => (M i i).re) (Unitary.coe_mul_star_self U)
  simpa [unitaryWeights, Matrix.mul_apply, Matrix.star_apply, Complex.mul_conj] using h

lemma unitaryWeights_col_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) (j : ι) : ∑ i, unitaryWeights U i j = 1 := by
  have h := congrArg (fun M : Matrix ι ι ℂ => (M j j).re) (Unitary.coe_star_mul_self U)
  simpa [unitaryWeights, Matrix.mul_apply, Matrix.star_apply, mul_comm, Complex.mul_conj] using h

/-- The diagonal entries of a unitarily conjugated real diagonal matrix are
exactly its unistochastic averages. -/
lemma diagonal_unitary_conjugate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℝ) (U : unitary (Matrix ι ι ℂ)) (i : ι) :
    (((U : Matrix ι ι ℂ) * Matrix.diagonal (fun j => (p j : ℂ)) *
      (star U : Matrix ι ι ℂ)) i i).re = ∑ j, unitaryWeights U i j * p j := by
  classical
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.star_apply]
  rw [← Complex.coe_reAddGroupHom, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (((U : Matrix ι ι ℂ) i j * (p j : ℂ)) *
    star ((U : Matrix ι ι ℂ) i j)).re = _
  have hm : (((U : Matrix ι ι ℂ) i j * (p j : ℂ)) *
      star ((U : Matrix ι ι ℂ) i j)) =
      (((U : Matrix ι ι ℂ) i j * star ((U : Matrix ι ι ℂ) i j)) * (p j : ℂ)) := by ring
  rw [hm]
  simp [unitaryWeights, Complex.mul_conj]

/-- Genuine von Neumann entropy is at most the Shannon entropy of diagonal
measurement probabilities in any fixed orthonormal basis. -/
theorem DensityMatrix.vonNeumann_le_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : DensityMatrix ι) :
    ρ.vonNeumann ≤ shannon (fun i => (ρ.matrix i i).re) := by
  let U := ρ.positive.isHermitian.eigenvectorUnitary
  have hd (i : ι) : (ρ.matrix i i).re = ∑ j, unitaryWeights U i j * ρ.weights j := by
    rw [ρ.positive.isHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
    exact diagonal_unitary_conjugate ρ.weights U i
  change shannon ρ.weights ≤ _
  simp_rw [hd]
  exact shannon_le_of_doublyStochastic ρ.weights ρ.weights_nonneg
    (unitaryWeights U) (unitaryWeights_nonneg U) (unitaryWeights_row_sum U)
    (unitaryWeights_col_sum U)

/-- Genuine von Neumann entropy concavity. The hypothesis is an explicit
matrix convex-combination identity, not an entropy inequality. -/
theorem densityMatrix_entropy_concave {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (ρ : DensityMatrix ι) (σ : κ → DensityMatrix ι)
    (p : κ → ℝ) (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1)
    (hmixture : ρ.matrix = ∑ j, (p j : ℂ) • (σ j).matrix) :
    (∑ j, p j * (σ j).vonNeumann) ≤ ρ.vonNeumann := by
  classical
  let U := ρ.positive.isHermitian.eigenvectorUnitary
  let V := star U
  let τ (j : κ) := (σ j).unitaryConjugate V
  have hdiag : (ρ.unitaryConjugate V).matrix =
      Matrix.diagonal (fun i => (ρ.weights i : ℂ)) :=
    ρ.positive.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hmat : (ρ.unitaryConjugate V).matrix = ∑ j, (p j : ℂ) • (τ j).matrix := by
    change (V : Matrix ι ι ℂ) * ρ.matrix * (star V : Matrix ι ι ℂ) = _
    rw [hmixture, Matrix.mul_sum, Matrix.sum_mul]
    simp only [τ, DensityMatrix.unitaryConjugate, Matrix.mul_smul, Matrix.smul_mul]
  have hd (i : ι) : ρ.weights i = ∑ j, p j * ((τ j).matrix i i).re := by
    have h := congrArg (fun M : Matrix ι ι ℂ => (M i i).re) (hdiag.symm.trans hmat)
    simpa [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Complex.mul_re] using h
  have hnonneg (j : κ) (i : ι) : 0 ≤ ((τ j).matrix i i).re :=
    (Complex.nonneg_iff.mp (τ j).positive.diag_nonneg).1
  calc
    (∑ j, p j * (σ j).vonNeumann) = ∑ j, p j * (τ j).vonNeumann := by
      simp only [τ, DensityMatrix.unitaryConjugate_entropy]
    _ ≤ ∑ j, p j * shannon (fun i => ((τ j).matrix i i).re) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
        (DensityMatrix.vonNeumann_le_diagonal (τ j)) (hp j))
    _ ≤ shannon (fun i => ∑ j, p j * ((τ j).matrix i i).re) :=
      shannon_mixture_concave p hp hsum _ hnonneg
    _ = ρ.vonNeumann := by
      simp_rw [← hd]
      rfl

/-- Concavity stated for the verified state mixture constructor. -/
theorem densityMatrix_mixture_entropy_concave {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ]
    (p : κ → ℝ) (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1)
    (σ : κ → DensityMatrix ι) :
    (∑ j, p j * (σ j).vonNeumann) ≤ (DensityMatrix.mixture p hp hsum σ).vonNeumann :=
  densityMatrix_entropy_concave _ σ p hp hsum rfl

lemma rightGram_diagonal_re {ι κ : Type*} [Fintype ι] (A : Matrix ι κ ℂ) (j : κ) :
    ((Aᴴ * A) j j).re = ∑ i, Complex.normSq (A i j) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, mul_comm, Complex.mul_conj]

/-- The entropy of an actual normalized Gram output is bounded by the
Shannon entropy of its column squared norms. This is the pure-ensemble
entropy bound without any assumed entropy law. -/
theorem bipartiteLeft_entropy_le_shannon {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι κ ℂ) (hnorm : (A * Aᴴ).trace = 1)
    (p : κ → ℝ) (hcolumns : ∀ j, ∑ i, Complex.normSq (A i j) = p j) :
    (bipartiteLeft A hnorm).vonNeumann ≤ shannon p := by
  calc
    (bipartiteLeft A hnorm).vonNeumann = (bipartiteRight A hnorm).vonNeumann :=
      bipartite_entropy_eq A hnorm
    _ ≤ shannon (fun j => ((bipartiteRight A hnorm).matrix j j).re) :=
      DensityMatrix.vonNeumann_le_diagonal (bipartiteRight A hnorm)
    _ = shannon p := by
      congr 1
      funext j
      exact (rightGram_diagonal_re A j).trans (hcolumns j)

/-- Shannon's finite conditional chain rule, including zero weights. -/
theorem shannon_joint {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : κ → ℝ) (q : κ → ι → ℝ) (hq : ∀ j, ∑ i, q j i = 1) :
    shannon (fun ji : κ × ι => p ji.1 * q ji.1 ji.2) =
      shannon p + ∑ j, p j * shannon (q j) := by
  simp only [shannon_eq_sum_negMulLog, Fintype.sum_prod_type, Real.negMulLog_mul,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hq, one_mul]

/-- A concrete amplitude matrix refining each mixed component into its
spectral pure-state ensemble. -/
def ensembleAmplitude {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (p : κ → ℝ) (σ : κ → DensityMatrix ι) : Matrix ι (κ × ι) ℂ :=
  fun i jk => (Real.sqrt (p jk.1 * (σ jk.1).weights jk.2) : ℂ) *
    ((σ jk.1).positive.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) i jk.2

lemma densityMatrix_spectral_entry {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : DensityMatrix ι) (i l : ι) :
    ρ.matrix i l = ∑ k,
      (ρ.positive.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) i k *
      (ρ.weights k : ℂ) *
      star ((ρ.positive.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) l k) := by
  conv_lhs =>
    rw [ρ.positive.isHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply,
      Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.star_apply]
  rfl

lemma ensembleAmplitude_term {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (p : κ → ℝ) (hp : ∀ j, 0 ≤ p j) (σ : κ → DensityMatrix ι)
    (i l : ι) (j : κ) (k : ι) :
    ensembleAmplitude p σ i (j,k) * star (ensembleAmplitude p σ l (j,k)) =
      (p j : ℂ) *
      (((σ j).positive.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) i k *
      ((σ j).weights k : ℂ) *
      star (((σ j).positive.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) l k)) := by
  have hw : 0 ≤ p j * (σ j).weights k := mul_nonneg (hp j) ((σ j).weights_nonneg k)
  have hs : (Real.sqrt (p j * (σ j).weights k) : ℂ) *
      (Real.sqrt (p j * (σ j).weights k) : ℂ) = (p j * (σ j).weights k : ℝ) := by
    exact_mod_cast Real.mul_self_sqrt hw
  simp only [ensembleAmplitude, star_mul, Complex.star_def, Complex.conj_ofReal]
  calc
    _ = ((Real.sqrt (p j * (σ j).weights k) : ℂ) *
      (Real.sqrt (p j * (σ j).weights k) : ℂ)) *
      (((σ j).positive.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) i k *
        conj (((σ j).positive.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) l k)) := by ring
    _ = _ := by rw [hs, Complex.ofReal_mul]; ring

/-- The left Gram matrix of the actual spectral refinement is the original
convex combination of density matrices. -/
lemma ensembleAmplitude_leftGram {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (p : κ → ℝ) (hp : ∀ j, 0 ≤ p j) (σ : κ → DensityMatrix ι) :
    ensembleAmplitude p σ * (ensembleAmplitude p σ)ᴴ =
      ∑ j, (p j : ℂ) • (σ j).matrix := by
  classical
  ext i l
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simp_rw [ensembleAmplitude_term p hp σ i l]
  simp only [← Finset.mul_sum, ← densityMatrix_spectral_entry]

lemma ensembleAmplitude_columns_normSq {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (p : κ → ℝ) (hp : ∀ j, 0 ≤ p j) (σ : κ → DensityMatrix ι)
    (j : κ) (k : ι) :
    (∑ i, Complex.normSq (ensembleAmplitude p σ i (j,k))) = p j * (σ j).weights k := by
  have hw : 0 ≤ p j * (σ j).weights k := mul_nonneg (hp j) ((σ j).weights_nonneg k)
  simp only [ensembleAmplitude, Complex.normSq_mul, Complex.normSq_ofReal,
    Real.mul_self_sqrt hw]
  rw [← Finset.mul_sum]
  have hc := unitaryWeights_col_sum (σ j).positive.isHermitian.eigenvectorUnitary k
  unfold unitaryWeights at hc
  rw [hc, mul_one]

/-- Genuine quantum entropy of mixing, proved by spectral refinement into a
normalized rectangular amplitude matrix, equality of its two Gram entropies,
and the already proved diagonal pinching bound. Zero weights are allowed. -/
theorem densityMatrix_mixture_entropy_upper {ι κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (p : κ → ℝ) (hp : ∀ j, 0 ≤ p j) (hsum : ∑ j, p j = 1)
    (σ : κ → DensityMatrix ι) :
    (DensityMatrix.mixture p hp hsum σ).vonNeumann ≤
      shannon p + ∑ j, p j * (σ j).vonNeumann := by
  let A := ensembleAmplitude p σ
  have hleft : A * Aᴴ = (DensityMatrix.mixture p hp hsum σ).matrix :=
    ensembleAmplitude_leftGram p hp σ
  have hn : (A * Aᴴ).trace = 1 := by
    rw [hleft]
    exact (DensityMatrix.mixture p hp hsum σ).normalized
  have hstate : bipartiteLeft A hn = DensityMatrix.mixture p hp hsum σ :=
    DensityMatrix.ext hleft
  have hb := bipartiteLeft_entropy_le_shannon A hn
    (fun jk : κ × ι => p jk.1 * (σ jk.1).weights jk.2)
    (fun jk => ensembleAmplitude_columns_normSq p hp σ jk.1 jk.2)
  rw [hstate, shannon_joint p (fun j => (σ j).weights) (fun j => (σ j).weights_sum)] at hb
  exact hb

end

end Nonadditivity.EntropyMixtures


