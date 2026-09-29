-- Prove2me | Definitions.Def_Logic_ProofTheoryAndLogic_SelfReference_2
-- name    : Logic_ProofTheoryAndLogic_SelfReference_2
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:02:55.076405+00:00
-- url     : https://prove2.me/theorems/7fc06416-3dda-4541-9d32-19ad09508ecc
-- title:
--   Aether Catalog definitions — Logic_ProofTheoryAndLogic_SelfReference_2
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.ProofTheoryAndLogic.SelfReference.2`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/ProofTheoryAndLogic/SelfReference_2.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Logic.SelfReference_2

Auto-generated from theorem catalog database.
Domain: Logic
Declarations: 6
-/

noncomputable section

/-- The iteration sequence: f⁰(⊥), f¹(⊥), f²(⊥), ... -/
noncomputable def iterate_from_bot {α : Type*} [CompleteLattice α]
    (f : α → α) : ℕ → α
  | 0 => ⊥
  | n + 1 => f (iterate_from_bot f n)






end


