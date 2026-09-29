-- Prove2me | Definitions.Def_Bridges_BerggrenLanglandsBridge
-- name    : Bridges_BerggrenLanglandsBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:14:35.134357+00:00
-- url     : https://prove2.me/theorems/5239c46c-7c86-4024-83cc-3d4fe083e5df
-- title:
--   Aether Catalog definitions — Bridges_BerggrenLanglandsBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.BerggrenLanglandsBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/BerggrenLanglandsBridge.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Bridges.BerggrenLanglandsBridge

Auto-generated from theorem catalog database.
Domain: Bridges
Declarations: 26
-/

noncomputable section


/-- The 2×2 Euclid parameter matrices. -/
def M₁ : Matrix (Fin 2) (Fin 2) ℤ := !![2, -1; 1, 0]

/-- [Section: # CatalogBuild.Bridges.BerggrenLanglandsBridge
Auto-generated from theorem catalog database.
Domain: Bridges
Declarations: 26] -/
def M₂ : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 1, 0]

/-- [Section: # CatalogBuild.Bridges.BerggrenLanglandsBridge
Auto-generated from theorem catalog database.
Domain: Bridges
Declarations: 26] -/
def M₃ : Matrix (Fin 2) (Fin 2) ℤ := !![1, 2; 0, 1]






/-- Euclid's parametrization: (m,n) ↦ (m²-n², 2mn, m²+n²). -/
def euclidParam (m n : ℤ) : Fin 3 → ℤ :=
  ![m^2 - n^2, 2*m*n, m^2 + n^2]



/-- The Pythagorean quadratic form: Q(v) = v₀² + v₁² - v₂². -/
def quadForm (v : Fin 3 → ℤ) : ℤ := v 0 ^ 2 + v 1 ^ 2 - v 2 ^ 2






/-- The modular S matrix. -/
def modularS : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 0]




/-- M₃ = T² where T = [[1,1],[0,1]] is the standard generator. -/
def modularT : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, 1]




end


