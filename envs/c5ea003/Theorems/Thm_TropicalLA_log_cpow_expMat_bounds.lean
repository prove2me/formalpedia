-- Prove2me | Theorems.Thm_TropicalLA_log_cpow_expMat_bounds
-- name    : TropicalLA.log_cpow_expMat_bounds
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T11:00:34.849111+00:00
-- url     : https://prove2.me/theorems/3be03f40-725c-4e02-aea3-504e76da3a27
-- title:
--   Logarithmic form of the squeeze.
-- statement:
--   Logarithmic form of the squeeze.
--
--   ```lean
--   theorem TropicalLA.log_cpow_expMat_bounds{t : ℝ} (ht : 0 < t) (A : Matrix ι ι ℝ) (m : ℕ) (i j : ι) :
--       tpow A m i j ≤ Real.log (cpow (expMat t A) m i j) / t ∧
--         Real.log (cpow (expMat t A) m i j) / t
--           ≤ tpow A m i j + m * Real.log (Fintype.card ι) / t := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/MaslovDequantization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/MaslovDequantization.lean#L101

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

theorem TropicalLA.log_cpow_expMat_bounds{t : ℝ} (ht : 0 < t) (A : Matrix ι ι ℝ) (m : ℕ) (i j : ι) :
    tpow A m i j ≤ Real.log (cpow (expMat t A) m i j) / t ∧
      Real.log (cpow (expMat t A) m i j) / t
        ≤ tpow A m i j + m * Real.log (Fintype.card ι) / t := by sorry
