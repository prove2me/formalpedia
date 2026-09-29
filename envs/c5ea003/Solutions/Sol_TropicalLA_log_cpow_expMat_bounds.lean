-- Prove2me | solution 1 for TropicalLA.log_cpow_expMat_bounds
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:17:58.337975+00:00
-- url     : https://prove2.me/submissions/acd29431-0d8f-4a54-a0c3-960b673f1acf

-- Sol generated from Algebra/TropicalLinearAlgebra/MaslovDequantization.lean
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_MaslovDequantization
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
import Theorems.Thm_TropicalLA_cpow_expMat_bounds
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
    tpow A m i j ≤ Real.log (cpow (expMat t A) m i j) / t ∧
      Real.log (cpow (expMat t A) m i j) / t
        ≤ tpow A m i j + m * Real.log (Fintype.card ι) / t := by
  obtain ⟨hlow, hhigh⟩ := cpow_expMat_bounds ht A m i j
  have hposE : 0 < cpow (expMat t A) m i j := cpow_pos (fun a b => Real.exp_pos _) m i j
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast Fintype.card_pos
  constructor
  · rw [le_div_iff₀ ht]
    have := Real.log_le_log (Real.exp_pos _) hlow
    rw [Real.log_exp] at this
    linarith
  · rw [div_le_iff₀ ht]
    have hlog := Real.log_le_log hposE hhigh
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, Real.log_pow] at hlog
    have : m * Real.log (Fintype.card ι) / t * t = m * Real.log (Fintype.card ι) := by
      field_simp
    nlinarith [hlog, this]
