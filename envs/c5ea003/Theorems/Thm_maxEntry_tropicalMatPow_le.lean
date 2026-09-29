-- Prove2me | Theorems.Thm_maxEntry_tropicalMatPow_le
-- name    : maxEntry_tropicalMatPow_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:34:16.253565+00:00
-- url     : https://prove2.me/theorems/d8d8f92f-f88c-4f8d-9f7f-4755948f7e0a
-- title:
--   MaxEntry tropicalMatPow le
-- statement:
--   Formal statement of `maxEntry_tropicalMatPow_le` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem maxEntry_tropicalMatPow_le(hn : 0 < n)
--       (M : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (hk : 1 ≤ k) :
--       maxEntry hn (tropicalMatPow hn M k) ≤ k * maxEntry hn M := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/NeuralCoding/MaxPlusLemmas.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/NeuralCoding/MaxPlusLemmas.lean#L78

-- Thm stub generated from Bridges/NeuralCoding/MaxPlusLemmas.lean
import Mathlib
import Definitions.Def_Bridges_NeuralCoding_MaxPlusDefs

/-!
# Max-Plus Algebra: Structural Lemmas

Basic structural properties of max-plus matrix operations.
-/

noncomputable section

open Finset BigOperators

variable {n : ℕ}








/-
The diagonal entry `(M^k) i i ≥ k * M i i` (by self-loop path).
-/

/-
Every entry of the tropical product is at most `maxEntry A + maxEntry B`.
-/

/-
Max entry of `M^k` is bounded by `k * maxEntry M` for `k ≥ 1`.
-/

theorem maxEntry_tropicalMatPow_le(hn : 0 < n)
    (M : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (hk : 1 ≤ k) :
    maxEntry hn (tropicalMatPow hn M k) ≤ k * maxEntry hn M := by sorry
