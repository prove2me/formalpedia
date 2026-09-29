-- Prove2me | Definitions.Def_Logic_GameTheory_HolographicSearch
-- name    : Logic_GameTheory_HolographicSearch
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:54:30.685411+00:00
-- url     : https://prove2.me/theorems/8a51f641-3a64-4920-adc8-07ce9fdd3ae4
-- title:
--   Aether Catalog definitions — Logic_GameTheory_HolographicSearch
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.GameTheory.HolographicSearch`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/GameTheory/HolographicSearch.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Logic.HolographicSearch

Auto-generated from theorem catalog database.
Domain: Logic
Declarations: 15
-/

noncomputable section












/-- A proof is k-resilient if removing any k steps still yields a valid
sub-proof of the conclusion. -/
def isResilient (n k : ℕ) (essential : Finset (Fin n)) : Prop :=
  ∀ removed : Finset (Fin n), removed.card ≤ k →
    ∃ surviving : Finset (Fin n),
      essential ⊆ surviving ∧ surviving.card ≥ n - k




end


