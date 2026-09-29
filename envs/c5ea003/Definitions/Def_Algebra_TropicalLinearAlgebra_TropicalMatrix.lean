-- Prove2me | Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
-- name    : Algebra_TropicalLinearAlgebra_TropicalMatrix
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T10:16:27.793928+00:00
-- url     : https://prove2.me/theorems/c83ee3aa-2f97-4894-94a0-ca35dfa3cb0b
-- title:
--   Aether Catalog definitions — Algebra_TropicalLinearAlgebra_TropicalMatrix
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.TropicalLinearAlgebra.TropicalMatrix`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/TropicalLinearAlgebra/TropicalMatrix.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_MaxPlusSemiring
/-
# Tropical (max-plus) matrices with finite entries

For matrices with entries in `ℝ` (i.e. no `-∞` entries) tropical multiplication is

  `(A ⊗ B) i j = max_k (A i k + B k j)`,

implemented with `Finset.sup'`.  We prove

* `tmul_assoc` : tropical matrix multiplication is associative (a hands-on proof,
  independent of the semiring instance);
* `tmul_embed`  : this operation agrees with multiplication in `Matrix ι ι (MaxPlus ℝ)`,
  so the two developments are coherent;
* `tpow_isGreatest` : **max-plus powers compute optimal paths** — the `(i,j)` entry of
  `A^{⊗(m+1)}` is the maximal weight of a length-`(m+1)` walk from `i` to `j`
  (the algebraic form of the Bellman dynamic-programming principle).
-/

namespace TropicalLA

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Tropical (max-plus) matrix product: `(A ⊗ B) i j = max_k (A i k + B k j)`. -/
noncomputable def tmul (A B : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun i j => Finset.univ.sup' Finset.univ_nonempty fun k => A i k + B k j

/-- Tropical matrix-vector product: `(A ⊗ v) i = max_j (A i j + v j)`. -/
noncomputable def tmulVec (A : Matrix ι ι ℝ) (v : ι → ℝ) : ι → ℝ :=
  fun i => Finset.univ.sup' Finset.univ_nonempty fun j => A i j + v j








section Embedding

/-- Embed a finite-entry real matrix into the max-plus semiring `MaxPlus ℝ`. -/
def embed (A : Matrix ι ι ℝ) : Matrix ι ι (MaxPlus ℝ) :=
  fun i j => MaxPlus.ofBot ((A i j : ℝ) : WithBot ℝ)



end Embedding

section Paths

/-- Tropical powers: `tpow A m = A^{⊗(m+1)}`. -/
noncomputable def tpow (A : Matrix ι ι ℝ) : ℕ → Matrix ι ι ℝ
  | 0 => A
  | (m + 1) => tmul (tpow A m) A

/-- The weight of the length-`m` walk `p 0 → p 1 → ⋯ → p m`. -/
def pathWeight (A : Matrix ι ι ℝ) (p : ℕ → ι) (m : ℕ) : ℝ :=
  ∑ t ∈ Finset.range m, A (p t) (p (t + 1))


end Paths

end TropicalLA


