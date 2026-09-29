-- Prove2me | Theorems.Thm_TropicalLA_cpow_expMat_bounds
-- name    : TropicalLA.cpow_expMat_bounds
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:59:41.772732+00:00
-- url     : https://prove2.me/theorems/8c19e135-c1f3-4595-98a8-fd6720b051b5
-- title:
--   Squeeze between the classical and the tropical power.
-- statement:
--   **Squeeze between the classical and the tropical power.**  Every entry of the
--   `(m+1)`-st ordinary power of the Boltzmann lift lies between the tropical value and
--   `n^m` times it.
--
--   ```lean
--   theorem TropicalLA.cpow_expMat_bounds{t : ℝ} (ht : 0 < t) (A : Matrix ι ι ℝ) (m : ℕ) (i j : ι) :
--       Real.exp (t * tpow A m i j) ≤ cpow (expMat t A) m i j ∧
--         cpow (expMat t A) m i j ≤ (Fintype.card ι : ℝ) ^ m * Real.exp (t * tpow A m i j) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/MaslovDequantization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/MaslovDequantization.lean#L40

-- Thm stub generated from Algebra/TropicalLinearAlgebra/MaslovDequantization.lean
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_MaslovDequantization
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
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

theorem TropicalLA.cpow_expMat_bounds{t : ℝ} (ht : 0 < t) (A : Matrix ι ι ℝ) (m : ℕ) (i j : ι) :
    Real.exp (t * tpow A m i j) ≤ cpow (expMat t A) m i j ∧
      cpow (expMat t A) m i j ≤ (Fintype.card ι : ℝ) ^ m * Real.exp (t * tpow A m i j) := by sorry
