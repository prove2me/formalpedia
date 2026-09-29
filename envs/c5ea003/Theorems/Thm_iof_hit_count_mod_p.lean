-- Prove2me | Theorems.Thm_iof_hit_count_mod_p
-- name    : iof_hit_count_mod_p
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T20:01:45.224578+00:00
-- url     : https://prove2.me/theorems/793434cc-3b8a-47a1-bec6-df48780c7083
-- title:
--   Iof hit count mod p
-- statement:
--   Formal statement of `iof_hit_count_mod_p` from the Aether Catalog (MachineLearning). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem iof_hit_count_mod_p(p : ℕ) (hp : Nat.Prime p) (hp_odd : p ≠ 2) :
--       haveI : Fact (Nat.Prime p) := ⟨hp⟩
--       (Finset.univ.filter (fun k : ZMod p => (2 : ZMod p) * k = 1 ∨ (2 : ZMod p) * k = -1)).card = 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/Neural/NeuralFactorSearch.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/Neural/NeuralFactorSearch.lean#L74

-- Thm stub generated from MachineLearning/Neural/NeuralFactorSearch.lean
import Mathlib

/-! # CatalogBuild.MachineLearning.Neural.NeuralFactorSearch

Auto-generated from theorem catalog database.
Domain: MachineLearning/Neural
Declarations: 8
-/

theorem iof_hit_count_mod_p(p : ℕ) (hp : Nat.Prime p) (hp_odd : p ≠ 2) :
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    (Finset.univ.filter (fun k : ZMod p => (2 : ZMod p) * k = 1 ∨ (2 : ZMod p) * k = -1)).card = 2 := by sorry
