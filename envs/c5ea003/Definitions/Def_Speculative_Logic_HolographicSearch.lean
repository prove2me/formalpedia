-- Prove2me | Definitions.Def_Speculative_Logic_HolographicSearch
-- name    : Speculative_Logic_HolographicSearch
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:32:38.784903+00:00
-- url     : https://prove2.me/theorems/c4cb2732-09ef-4992-8f8e-819621bf9eb2
-- title:
--   Aether Catalog definitions — Speculative_Logic_HolographicSearch
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.Logic.HolographicSearch`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/Logic/HolographicSearch.lean by skeleton subtraction
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


