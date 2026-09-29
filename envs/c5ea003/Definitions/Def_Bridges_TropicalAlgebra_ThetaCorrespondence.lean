-- Prove2me | Definitions.Def_Bridges_TropicalAlgebra_ThetaCorrespondence
-- name    : Bridges_TropicalAlgebra_ThetaCorrespondence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:41:37.323716+00:00
-- url     : https://prove2.me/theorems/9d95ffcc-1e00-450d-9904-bdc98db1889c
-- title:
--   Aether Catalog definitions — Bridges_TropicalAlgebra_ThetaCorrespondence
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalAlgebra.ThetaCorrespondence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalAlgebra/ThetaCorrespondence.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Tropical.Langlands.ThetaCorrespondence

Auto-generated from theorem catalog database.
Domain: Tropical/Langlands
Declarations: 25
-/

noncomputable section

/-- [Section: # CatalogBuild.Tropical.Langlands.ThetaCorrespondence
Auto-generated from theorem catalog database.
Domain: Tropical/Langlands
Declarations: 25] -/
def tropicalQuadraticForm (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, x i ^ 2

/-- [Section: # CatalogBuild.Tropical.Langlands.ThetaCorrespondence
Auto-generated from theorem catalog database.
Domain: Tropical/Langlands
Declarations: 25] -/
def tropicalSymplecticForm (n : ℕ) (x y : Fin n → ℝ × ℝ) : ℝ :=
  ∑ i : Fin n, ((x i).1 * (y i).2 - (x i).2 * (y i).1)





def tropicalThetaKernel (m n : ℕ) (a : Fin m → ℝ) (b : Fin n → ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, a i * b j






structure LParam (n : ℕ) where
  values : Fin n → ℝ
  sorted : ∀ i j : Fin n, i ≤ j → values i ≥ values j

def tropicalLValue (n : ℕ) (p : LParam n) (s : ℝ) : ℝ :=
  ∑ i : Fin n, p.values i * s


structure TropicalDualPair where
  m : ℕ
  n : ℕ

def TropicalDualPair.swap (P : TropicalDualPair) : TropicalDualPair :=
  { m := P.n, n := P.m }


def TropicalDualPair.size (P : TropicalDualPair) : ℕ := P.m * P.n


def tropicalWeilAction (n : ℕ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => -x i



structure SeeSaw where
  pair1 : TropicalDualPair
  pair2 : TropicalDualPair
  compatible : pair1.m = pair2.n


end


