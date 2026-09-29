-- Prove2me | Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalGelfand
-- name    : Algebra_TropicalLinearAlgebra_TropicalGelfand
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:29:51.21678+00:00
-- url     : https://prove2.me/theorems/87883e91-f362-41fa-aa10-d04b7404f59d
-- title:
--   Aether Catalog definitions — Algebra_TropicalLinearAlgebra_TropicalGelfand
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.TropicalLinearAlgebra.TropicalGelfand`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/TropicalLinearAlgebra/TropicalGelfand.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalPerronFrobenius
/-
# A tropical Gelfand formula: growth rate of matrix powers

Classically the spectral radius of a matrix is the limit of `‖A^m‖^{1/m}`.  In the
max-plus world exponentiation becomes multiplication, and the statement becomes

  `‖A^{⊗ m}‖ / m → λ(A)`,

where `‖·‖` is the largest entry and `λ(A)` is the maximum cycle mean.  This file
proves the sharp two-sided form: the largest entry of `A^{⊗(m+1)}` differs from
`(m+1)·λ` by at most the *spread* `max v - min v` of a tropical eigenvector,
uniformly in `m`, hence the normalised growth rate converges to `λ`.

The bridge is that the eigenvector is preserved by the tropical action:
`A^{⊗(m+1)} ⊗ v = ((m+1)·λ) ⊗ v` (`IsTropEigen.tmulVec_tpow`).
-/

namespace TropicalLA

open Filter Topology

variable {ι : Type*} [Fintype ι] [Nonempty ι]


namespace IsTropEigen

variable {A : Matrix ι ι ℝ} {lam : ℝ} {v : ι → ℝ}


end IsTropEigen

section Growth

variable (A : Matrix ι ι ℝ)

/-- The largest entry of `A^{⊗(m+1)}`: the tropical analogue of a matrix norm. -/
noncomputable def specNorm (m : ℕ) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty (α := ι))
    (fun i => Finset.univ.sup' (Finset.univ_nonempty (α := ι)) (fun j => tpow A m i j))

variable {A}





end Growth

end TropicalLA


