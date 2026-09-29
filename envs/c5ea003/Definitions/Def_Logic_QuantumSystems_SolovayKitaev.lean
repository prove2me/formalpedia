-- Prove2me | Definitions.Def_Logic_QuantumSystems_SolovayKitaev
-- name    : Logic_QuantumSystems_SolovayKitaev
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:07:10.241704+00:00
-- url     : https://prove2.me/theorems/8e480d01-1165-45f2-8607-71e98606f31d
-- title:
--   Aether Catalog definitions — Logic_QuantumSystems_SolovayKitaev
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.QuantumSystems.SolovayKitaev`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/QuantumSystems/SolovayKitaev.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Physics.Quantum.SolovayKitaev

Auto-generated from theorem catalog database.
Domain: Physics/Quantum
Declarations: 15
-/

noncomputable section






def skCommutator {G : Type*} [Group G] (u v : G) : G := u * v * u⁻¹ * v⁻¹






def skCayleyBall {G : Type*} [Group G] (S : Set G) (n : ℕ) : Set G :=
  {g | ∃ (words : List G), (∀ w ∈ words, w ∈ S ∨ w⁻¹ ∈ S) ∧
    words.length ≤ n ∧ words.prod = g}




end


