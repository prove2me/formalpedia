-- Prove2me | Theorems.Thm_TropicalLA_tmul_add_distrib
-- name    : TropicalLA.tmul_add_distrib
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T11:01:08.43089+00:00
-- url     : https://prove2.me/theorems/9077484c-fbb8-422d-a1e8-da1f9cf1f7b0
-- title:
--   Tropical multiplication distributes over the entrywise `max` of matrices.
-- statement:
--   Tropical multiplication distributes over the entrywise `max` of matrices.
--
--   ```lean
--   theorem TropicalLA.tmul_add_distrib(A B C : Matrix ι ι ℝ) (i j : ι) :
--       tmul A (fun i j => max (B i j) (C i j)) i j = max (tmul A B i j) (tmul A C i j) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/TropicalMatrix.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/TropicalMatrix.lean#L68

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

theorem TropicalLA.tmul_add_distrib(A B C : Matrix ι ι ℝ) (i j : ι) :
    tmul A (fun i j => max (B i j) (C i j)) i j = max (tmul A B i j) (tmul A C i j) := by sorry
