-- Prove2me | Definitions.Def_Speculative_Shared_Tribonacci
-- name    : Speculative_Shared_Tribonacci
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:34:58.234772+00:00
-- url     : https://prove2.me/theorems/1435bbba-31fb-4dbd-9f9a-7a986ae5533c
-- title:
--   Aether Catalog definitions — Speculative_Shared_Tribonacci
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.Shared.Tribonacci`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/Shared/Tribonacci.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Tribonacci

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 2
-/

/-- [Section: # CatalogBuild.Shared.Tribonacci
Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 2] -/
def tribonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => tribonacci (n + 2) + tribonacci (n + 1) + tribonacci n


