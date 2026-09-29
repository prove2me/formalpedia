-- Prove2me | Theorems.Thm_ECOC_nearest_codeword_unique_of_lt_half_minDist
-- name    : ECOC.nearest_codeword_unique_of_lt_half_minDist
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:46:51.466425+00:00
-- url     : https://prove2.me/theorems/813b6774-fb97-40ca-bf27-96fa25352cd7
-- title:
--   A word at distance strictly less than half the minimum distance has a unique
-- statement:
--   A word at distance strictly less than half the minimum distance has a unique
--   nearest codeword.
--
--   ```lean
--   theorem ECOC.nearest_codeword_unique_of_lt_half_minDist    {n m δ : ℕ} {code : Fin n → Fin m → Bool} {y : Fin m → Bool} {c : Fin n}
--       (hδ : MinDistAtLeast code δ)
--       (hy : 2 * hammingDist y (code c) < δ) :
--       nearestUnique code y c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/HammingCode.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/HammingCode.lean#L24

-- Thm stub generated from Bridges/HammingCode.lean
import Mathlib
import Definitions.Def_Bridges_HammingCode

open Finset

open ECOC

theorem ECOC.nearest_codeword_unique_of_lt_half_minDist    {n m δ : ℕ} {code : Fin n → Fin m → Bool} {y : Fin m → Bool} {c : Fin n}
    (hδ : MinDistAtLeast code δ)
    (hy : 2 * hammingDist y (code c) < δ) :
    nearestUnique code y c := by sorry
