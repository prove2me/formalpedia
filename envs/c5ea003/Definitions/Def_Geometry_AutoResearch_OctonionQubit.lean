-- Prove2me | Definitions.Def_Geometry_AutoResearch_OctonionQubit
-- name    : Geometry_AutoResearch_OctonionQubit
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T23:50:49.077325+00:00
-- url     : https://prove2.me/theorems/4bb3f8c9-a392-466f-8341-94ddce9e34fa
-- title:
--   Aether Catalog definitions — Geometry_AutoResearch_OctonionQubit
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.AutoResearch.OctonionQubit`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/AutoResearch/OctonionQubit.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Algebra.DivisionAlgebras.OctonionQubit

Auto-generated from theorem catalog database.
Domain: Algebra/DivisionAlgebras
Declarations: 15
-/


noncomputable section

/-- A point on the unit (n-1)-sphere in ℝⁿ: a vector with norm 1. -/
def UnitSphere (n : ℕ) := {v : Fin n → ℝ // ∑ i, v i ^ 2 = 1}
















/-- The inner product on ℝⁿ. -/
def innerProduct (n : ℕ) (v w : Fin n → ℝ) : ℝ :=
  ∑ i, v i * w i




/-- The squared norm. -/
def sqNorm (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  ∑ i, v i ^ 2








/-- The Born rule for octonionic measurement: the probability of measuring
state φ given state ψ is the squared norm of their inner product. -/
noncomputable def bornProbability (n : ℕ) (ψ φ : UnitSphere n) : ℝ :=
  (innerProduct n ψ.val φ.val) ^ 2












/-- Stereographic projection from the "north pole" (0,...,0,1) of Sⁿ.
Maps ℝⁿ to Sⁿ (embedded in ℝⁿ⁺¹). -/
noncomputable def stereoProj (n : ℕ) (t : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  let s := ∑ i, t i ^ 2
  fun i =>
    if h : i.val < n then
      2 * t ⟨i.val, h⟩ / (1 + s)
    else
      (s - 1) / (1 + s)












/-- The Fano plane encodes octonionic multiplication.
fanoTriples lists the 7 lines of the Fano plane as ordered triples
(i, j, k) meaning eᵢ * eⱼ = eₖ. -/
def fanoTriples : List (Fin 7 × Fin 7 × Fin 7) :=
  [(⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩),
   (⟨0, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩),
   (⟨0, by omega⟩, ⟨6, by omega⟩, ⟨5, by omega⟩),
   (⟨1, by omega⟩, ⟨3, by omega⟩, ⟨5, by omega⟩),  -- corrected sign convention
   (⟨1, by omega⟩, ⟨4, by omega⟩, ⟨6, by omega⟩),
   (⟨2, by omega⟩, ⟨3, by omega⟩, ⟨6, by omega⟩),
   (⟨2, by omega⟩, ⟨4, by omega⟩, ⟨5, by omega⟩)]







end


