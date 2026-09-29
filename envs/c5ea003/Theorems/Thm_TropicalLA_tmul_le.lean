-- Prove2me | Theorems.Thm_TropicalLA_tmul_le
-- name    : TropicalLA.tmul_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:59:54.621073+00:00
-- url     : https://prove2.me/theorems/d33fdb06-f48c-49ff-8a73-d7f03635b8e4
-- title:
--   Tmul le
-- statement:
--   Formal statement of `TropicalLA.tmul_le` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem TropicalLA.tmul_le{A B : Matrix ι ι ℝ} {i j : ι} {c : ℝ} (h : ∀ k, A i k + B k j ≤ c) :
--       tmul A B i j ≤ c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/TropicalLinearAlgebra/TropicalMatrix.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/TropicalLinearAlgebra/TropicalMatrix.lean#L35

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

theorem TropicalLA.tmul_le{A B : Matrix ι ι ℝ} {i j : ι} {c : ℝ} (h : ∀ k, A i k + B k j ≤ c) :
    tmul A B i j ≤ c := by sorry
