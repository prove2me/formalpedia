-- Prove2me | Definitions.Def_Bridges_TropicalAlgebra_LocalLanglands
-- name    : Bridges_TropicalAlgebra_LocalLanglands
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:41:18.021341+00:00
-- url     : https://prove2.me/theorems/b42975f3-616b-4dcc-b7dc-5046bf01cbbc
-- title:
--   Aether Catalog definitions — Bridges_TropicalAlgebra_LocalLanglands
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.TropicalAlgebra.LocalLanglands`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/TropicalAlgebra/LocalLanglands.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Tropical.Langlands.LocalLanglands

Auto-generated from theorem catalog database.
Domain: Tropical/Langlands
Declarations: 22
-/

noncomputable section

/-- A tropical Weil-Deligne representation of dimension n -/
structure TropicalWDRep (n : ℕ) where
  frobeniusEigenvalues : Fin n → ℝ
  sorted : ∀ i j : Fin n, i ≤ j → frobeniusEigenvalues i ≤ frobeniusEigenvalues j
  monodromyRank : ℕ
  monodromy_bound : monodromyRank ≤ n

/-- A tropical smooth representation of GL_n(F) -/
structure TropicalSmoothRep (n : ℕ) where
  satakeParameters : Fin n → ℝ
  sorted : ∀ i j : Fin n, i ≤ j → satakeParameters i ≤ satakeParameters j
  conductor : ℕ

/-- The tropical local Langlands map -/
def tropicalLLC (n : ℕ) (rho : TropicalWDRep n) : TropicalSmoothRep n where
  satakeParameters := rho.frobeniusEigenvalues
  sorted := rho.sorted
  conductor := rho.monodromyRank



/-- Tropical local L-factor -/
def tropicalLocalL (n : ℕ) (rho : TropicalWDRep n) (s : ℝ) : ℝ :=
  (∑ i : Fin n, rho.frobeniusEigenvalues i) * s






/-- Newton polygon point -/
def newtonPolygonPoint (n : ℕ) (rho : TropicalWDRep n) (k : Fin n) : ℝ × ℝ :=
  (k.val, ∑ i ∈ Finset.filter (· ≤ k) Finset.univ, rho.frobeniusEigenvalues i)



/-- A WD rep is unramified if monodromy rank = 0 -/
def isUnramified (n : ℕ) (rho : TropicalWDRep n) : Prop :=
  rho.monodromyRank = 0


/-- Unramified WD rep with constant eigenvalues -/
def unramifiedWDRep (n : ℕ) (a : ℝ) : TropicalWDRep n where
  frobeniusEigenvalues := fun _ => a
  sorted := fun _ _ _ => le_refl _
  monodromyRank := 0
  monodromy_bound := Nat.zero_le _



/-- Global-to-local restriction -/
def globalToLocal (n : ℕ) (globalParams : Fin n → ℝ)
    (hsorted : ∀ i j : Fin n, i ≤ j → globalParams i ≤ globalParams j) :
    TropicalWDRep n where
  frobeniusEigenvalues := globalParams
  sorted := hsorted
  monodromyRank := 0
  monodromy_bound := Nat.zero_le _



end


