-- Prove2me | Theorems.Thm_XORFullTilt_Hardness_Supplement_exact_undecidable
-- name    : XORFullTilt.Hardness.Supplement.exact_undecidable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:27:56.729125+00:00
-- url     : https://prove2.me/theorems/2d2c60d2-1658-4274-bb84-a664fd1d02eb
-- title:
--   Theorem 4.1 — exact-threshold undecidability
-- statement:
--   There is no total computable Boolean decision procedure that, for every explicit tilted XOR game $G$, correctly decides
--   $$\omega^*(G)\ge\frac34.$$
--   The negative case is $\omega^*(G)<3/4$; these cases partition all inputs, with no promise band. The value is the actual supremum over all finite-dimensional tensor-product POVM strategies, without an optimal-strategy attainment assumption. This gives the ungapped companion to the mission's gapped goal.
--
--   Differences from the source:
--   - encoding: explicit finite descriptions of tilted XOR games → the published natural-number rational table encoding, with its total malformed-input convention; reason: this reuses the live mission input model; the value remains the supremum over all finite-dimensional POVM strategies
-- source:
--   Richard Cleve, Eric Culf, Aviv Taller, XOR Games at Full Tilt: The Hardness of Binary Nonlocal Games, STOC 2027 submission #396 (October 2026), p. 20, Theorem 4.1

import Mathlib
import Definitions.Def_XORFullTilt_Hardness_EffectiveGames

open Matrix Kronecker

namespace XORFullTilt.Hardness.Supplement

/-- Theorem 4.1, for the supremum over all finite-dimensional POVM strategies. -/
theorem exact_undecidable :
    ¬ ∃ D : ℕ → Bool, Computable D ∧
      ∀ n, D n = true ↔ explicitValue n ≥ (3/4 : ℝ) := by sorry
end XORFullTilt.Hardness.Supplement
