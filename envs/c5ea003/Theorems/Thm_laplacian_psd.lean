-- Prove2me | Theorems.Thm_laplacian_psd
-- name    : laplacian_psd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:34:02.629752+00:00
-- url     : https://prove2.me/theorems/a4388cad-3f1d-4fa8-be79-ddb064cf2eae
-- title:
--   [Section: # CatalogBuild.Bridges.HilbertPolyaOperator
-- statement:
--   [Section: # CatalogBuild.Bridges.HilbertPolyaOperator
--   Auto-generated from theorem catalog database.
--   Domain: Bridges
--   Declarations: 15]
--
--   ```lean
--   theorem laplacian_psd{n : ℕ}
--       (A : Matrix (Fin n) (Fin n) ℝ)
--       (hA_symm : A.IsSymm)
--       (hA_nonneg : ∀ i j, A i j ≥ 0)
--       (D : Matrix (Fin n) (Fin n) ℝ)
--       (hD : ∀ i, D i i = ∑ j, A i j)
--       (hD_diag : ∀ i j, i ≠ j → D i j = 0) :
--       ∀ v : Fin n → ℝ, v ⬝ᵥ ((D - A).mulVec v) ≥ 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/HilbertPolyaOperator.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/HilbertPolyaOperator.lean#L23

-- Thm stub generated from Bridges/HilbertPolyaOperator.lean
import Mathlib
import Definitions.Def_Bridges_HilbertPolyaOperator

/-! # CatalogBuild.Bridges.HilbertPolyaOperator

Auto-generated from theorem catalog database.
Domain: Bridges
Declarations: 15
-/

noncomputable section

theorem laplacian_psd{n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA_symm : A.IsSymm)
    (hA_nonneg : ∀ i j, A i j ≥ 0)
    (D : Matrix (Fin n) (Fin n) ℝ)
    (hD : ∀ i, D i i = ∑ j, A i j)
    (hD_diag : ∀ i j, i ≠ j → D i j = 0) :
    ∀ v : Fin n → ℝ, v ⬝ᵥ ((D - A).mulVec v) ≥ 0 := by sorry
