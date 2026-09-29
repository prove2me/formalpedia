-- Prove2me | Theorems.Thm_TropicalLA_tmul_assoc
-- name    : TropicalLA.tmul_assoc
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T11:00:04.054981+00:00
-- url     : https://prove2.me/theorems/03cd48c4-fe64-4a8b-9170-8a00690023f6
-- title:
--   Associativity of tropical matrix multiplication, proved directly from the
-- statement:
--   **Associativity of tropical matrix multiplication**, proved directly from the
--   `max`-of-sums formula.
--
--   ```lean
--   theorem TropicalLA.tmul_assoc(A B C : Matrix ι ι ℝ) : tmul (tmul A B) C = tmul A (tmul B C) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/TropicalMatrix.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/TropicalMatrix.lean#L52

-- Thm stub generated from Algebra/TropicalLinearAlgebra/TropicalMatrix.lean
import Mathlib
import Definitions.Def_Algebra_TropicalLinearAlgebra_MaxPlusSemiring
import Definitions.Def_Algebra_TropicalLinearAlgebra_TropicalMatrix
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

open TropicalLA

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem TropicalLA.tmul_assoc(A B C : Matrix ι ι ℝ) : tmul (tmul A B) C = tmul A (tmul B C) := by sorry
