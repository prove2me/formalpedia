-- Prove2me | Definitions.Def_Algebra_TropicalLinearAlgebra_MaslovDequantization
-- name    : Algebra_TropicalLinearAlgebra_MaslovDequantization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T10:18:39.461855+00:00
-- url     : https://prove2.me/theorems/d8b926a0-09fe-4dd2-9865-946e15058821
-- title:
--   Aether Catalog definitions — Algebra_TropicalLinearAlgebra_MaslovDequantization
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.TropicalLinearAlgebra.MaslovDequantization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/TropicalLinearAlgebra/MaslovDequantization.lean by skeleton subtraction
import Mathlib
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

namespace TropicalLA

open Filter Topology

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The Boltzmann/exponential lift of a max-plus matrix at inverse temperature `t`. -/
noncomputable def expMat (t : ℝ) (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => Real.exp (t * A i j)

/-- Classical (ordinary) matrix powers, indexed like `tpow`: `cpow X m = X ^ (m+1)`. -/
noncomputable def cpow (X : Matrix ι ι ℝ) : ℕ → Matrix ι ι ℝ
  | 0 => X
  | (m + 1) => cpow X m * X





end TropicalLA


