-- Prove2me | solution 1 for TropicalLA.cpow_expMat_bounds
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:15:39.47261+00:00
-- url     : https://prove2.me/submissions/1c0502ff-ebfd-464b-b77b-c21180b2e88e

-- Sol generated from Algebra/TropicalLinearAlgebra/MaslovDequantization.lean
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_MaslovDequantization
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
import Theorems.Thm_TropicalLA_exists_tmul_eq
import Theorems.Thm_TropicalLA_le_tmul
/-
# Maslov dequantization: classical matrix powers converge to tropical ones

Tropical algebra is the "zero-temperature limit" of ordinary algebra.  Concretely, for
`t > 0` let `E_t(A)` be the *classical* nonnegative matrix with entries `exp (t · A i j)`.
Then ordinary matrix powers of `E_t(A)` are squeezed between the tropical power and
`n^m` times it:

  `exp (t · (A^{⊗(m+1)}) i j) ≤ (E_t(A)^{m+1}) i j ≤ n^m · exp (t · (A^{⊗(m+1)}) i j)`,

so that `log ((E_t(A)^{m+1}) i j) / t → (A^{⊗(m+1)}) i j` as `t → ∞`.  This is the
matrix form of Maslov dequantization, and it links the combinatorial optimum computed by
`tpow` with genuine analysis (`Real.exp`, `Real.log`, limits).
-/

open TropicalLA

open Filter Topology

variable {ι : Type*} [Fintype ι] [Nonempty ι]



theorem cpow_pos {X : Matrix ι ι ℝ} (hX : ∀ i j, 0 < X i j) (m : ℕ) (i j : ι) :
    0 < cpow X m i j := by
  induction m generalizing i j with
  | zero => exact hX i j
  | succ m ih =>
      rw [show cpow X (m + 1) = cpow X m * X from rfl, Matrix.mul_apply]
      exact Finset.sum_pos (fun k _ => mul_pos (ih i k) (hX k j)) Finset.univ_nonempty





open TropicalLA in
theorem solution{t : ℝ} (ht : 0 < t) (A : Matrix ι ι ℝ) (m : ℕ) (i j : ι) :
    Real.exp (t * tpow A m i j) ≤ cpow (expMat t A) m i j ∧
      cpow (expMat t A) m i j ≤ (Fintype.card ι : ℝ) ^ m * Real.exp (t * tpow A m i j) := by
  induction m generalizing i j with
  | zero =>
      constructor
      · exact le_of_eq rfl
      · simp [cpow, expMat, tpow]
  | succ m ih =>
      have hpos : ∀ (k : ι), 0 < expMat t A k j := fun k => Real.exp_pos _
      constructor
      · obtain ⟨k, hk⟩ := exists_tmul_eq (tpow A m) A i j
        have hterm : Real.exp (t * tpow A (m + 1) i j)
            ≤ cpow (expMat t A) m i k * expMat t A k j := by
          have h1 := (ih i k).1
          have h2 : Real.exp (t * tpow A (m + 1) i j)
              = Real.exp (t * tpow A m i k) * Real.exp (t * A k j) := by
            rw [← Real.exp_add]
            congr 1
            rw [show tpow A (m + 1) i j = tmul (tpow A m) A i j from rfl, hk]
            ring
          rw [h2]
          exact mul_le_mul_of_nonneg_right h1 (le_of_lt (Real.exp_pos _))
        refine le_trans hterm ?_
        rw [show cpow (expMat t A) (m + 1) = cpow (expMat t A) m * expMat t A from rfl,
          Matrix.mul_apply]
        refine Finset.single_le_sum (f := fun k => cpow (expMat t A) m i k * expMat t A k j)
          (fun k _ => ?_) (Finset.mem_univ k)
        exact le_of_lt (mul_pos (cpow_pos (fun a b => Real.exp_pos _) m i k) (hpos k))
      · rw [show cpow (expMat t A) (m + 1) = cpow (expMat t A) m * expMat t A from rfl,
          Matrix.mul_apply]
        have hbound : ∀ k ∈ (Finset.univ : Finset ι),
            cpow (expMat t A) m i k * expMat t A k j
              ≤ (Fintype.card ι : ℝ) ^ m * Real.exp (t * tpow A (m + 1) i j) := by
          intro k _
          have h1 := (ih i k).2
          have hle : tpow A m i k + A k j ≤ tpow A (m + 1) i j := le_tmul (tpow A m) A i j k
          have h2 : Real.exp (t * tpow A m i k) * Real.exp (t * A k j)
              ≤ Real.exp (t * tpow A (m + 1) i j) := by
            rw [← Real.exp_add]
            exact Real.exp_le_exp.mpr (by nlinarith)
          have h3 : cpow (expMat t A) m i k * expMat t A k j
              ≤ ((Fintype.card ι : ℝ) ^ m * Real.exp (t * tpow A m i k)) * Real.exp (t * A k j) :=
            mul_le_mul_of_nonneg_right h1 (le_of_lt (Real.exp_pos _))
          calc cpow (expMat t A) m i k * expMat t A k j
              ≤ ((Fintype.card ι : ℝ) ^ m * Real.exp (t * tpow A m i k)) * Real.exp (t * A k j) := h3
            _ = (Fintype.card ι : ℝ) ^ m * (Real.exp (t * tpow A m i k) * Real.exp (t * A k j)) := by
                ring
            _ ≤ (Fintype.card ι : ℝ) ^ m * Real.exp (t * tpow A (m + 1) i j) := by
                have : (0 : ℝ) ≤ (Fintype.card ι : ℝ) ^ m := by positivity
                exact mul_le_mul_of_nonneg_left h2 this
        calc ∑ k, cpow (expMat t A) m i k * expMat t A k j
            ≤ ∑ _k : ι, (Fintype.card ι : ℝ) ^ m * Real.exp (t * tpow A (m + 1) i j) :=
              Finset.sum_le_sum hbound
          _ = (Fintype.card ι : ℝ) ^ (m + 1) * Real.exp (t * tpow A (m + 1) i j) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              ring
