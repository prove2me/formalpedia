-- Prove2me | Definitions.Def_Tropical_TropicalAlgebra_AutomorphicBuildings
-- name    : Tropical_TropicalAlgebra_AutomorphicBuildings
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:33:01.187889+00:00
-- url     : https://prove2.me/theorems/f7753bec-fb0e-4628-af3a-8cc28e234020
-- title:
--   Aether Catalog definitions — Tropical_TropicalAlgebra_AutomorphicBuildings
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.TropicalAlgebra.AutomorphicBuildings`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/TropicalAlgebra/AutomorphicBuildings.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Tropical.Langlands.AutomorphicBuildings

Auto-generated from theorem catalog database.
Domain: Tropical/Langlands
Declarations: 23
-/

noncomputable section

/-- A vertex in the Bruhat-Tits building of GL_n -/
structure BuildingVertex (n : ℕ) where
  invariantFactors : Fin n → ℝ
  sorted : ∀ i j : Fin n, i ≤ j → invariantFactors i ≤ invariantFactors j

/-- The distance between two vertices -/
def buildingDistance (n : ℕ) (v w : BuildingVertex n) : ℝ :=
  ∑ i : Fin n, |v.invariantFactors i - w.invariantFactors i|




/-- An apartment in the building -/
structure Apartment (n : ℕ) where
  origin : Fin n → ℝ

/-- The standard apartment -/
def standardApartment (n : ℕ) : Apartment n where
  origin := fun _ => 0



/-- Tropical Laplacian at a vertex -/
def tropicalLaplacian (n : ℕ) (f : BuildingVertex n → ℝ) (v : BuildingVertex n)
    (neighbors : Finset (BuildingVertex n)) : ℝ :=
  (∑ w ∈ neighbors, f w) / neighbors.card - f v


/-- Tropical spherical function -/
def tropicalSpherical (n : ℕ) (s : ℝ) (v : BuildingVertex n) : ℝ :=
  s * ∑ i : Fin n, v.invariantFactors i




/-- Iwahori-Hecke generator (tropical version) -/
def iwahoriGenerator (q : ℝ) (_hq : q > 0) (x : ℝ) : ℝ :=
  min x (x + q)



/-- Depth of a building vertex (requires n ≥ 1) -/
def vertexDepth (n : ℕ) (hn : n ≥ 1) (v : BuildingVertex n) : ℝ :=
  v.invariantFactors ⟨n - 1, by omega⟩ - v.invariantFactors ⟨0, by omega⟩


/-- A special vertex has integer invariant factors -/
def isSpecialVertex (n : ℕ) (v : BuildingVertex n) : Prop :=
  ∀ i, ∃ k : ℤ, v.invariantFactors i = k



end


