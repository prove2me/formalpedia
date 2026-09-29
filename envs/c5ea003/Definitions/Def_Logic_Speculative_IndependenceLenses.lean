-- Prove2me | Definitions.Def_Logic_Speculative_IndependenceLenses
-- name    : Logic_Speculative_IndependenceLenses
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:07:39.490211+00:00
-- url     : https://prove2.me/theorems/c5e9e81c-5ef1-449e-b6e0-d8bd5b4823b9
-- title:
--   Aether Catalog definitions — Logic_Speculative_IndependenceLenses
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.Speculative.IndependenceLenses`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/Speculative/IndependenceLenses.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Speculative.IndependenceLenses

Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 10
-/







def primeCountDecidable (n : ℕ) : ℕ :=
  ((Finset.Icc 2 n).filter Nat.Prime).card


