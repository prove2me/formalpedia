-- Prove2me | Definitions.Def_Logic_PostQuantumSignatures
-- name    : Logic_PostQuantumSignatures
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T14:02:39.231905+00:00
-- url     : https://prove2.me/theorems/fae59894-83c1-4f44-b2a4-db7959e15958
-- title:
--   Aether Catalog definitions — Logic_PostQuantumSignatures
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.PostQuantumSignatures`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/PostQuantumSignatures.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Cryptography.QuantumSecurity.PostQuantumSignatures

Auto-generated from theorem catalog database.
Domain: Cryptography/QuantumSecurity
Declarations: 11
-/

noncomputable section



structure SISHardness where
  sisAdvantage : ℕ → ℝ
  isHard : ∀ c : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |sisAdvantage n| < (1 / (n : ℝ)) ^ c


noncomputable def blsSigSize : ℝ := 48

noncomputable def latticeSigSize (n : ℕ) : ℝ := 2 * (n : ℝ)






end


