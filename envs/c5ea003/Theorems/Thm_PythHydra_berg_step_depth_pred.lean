-- Prove2me | Theorems.Thm_PythHydra_berg_step_depth_pred
-- name    : PythHydra.berg_step_depth_pred
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T13:12:38.018129+00:00
-- url     : https://prove2.me/theorems/2dc89fc2-5859-4446-9385-5c890004928d
-- title:
--   From a non-empty hydra there is a Berggren chop dropping the depth potential by
-- statement:
--   From a non-empty hydra there is a Berggren chop dropping the depth potential by
--   exactly one.
--
--   ```lean
--   theorem PythHydra.berg_step_depth_pred{k : ℕ} {H : Multiset (ℤ × ℤ × ℤ)} (hH : H ≠ 0) :
--       ∃ H', BergChop k H H' ∧ Phi k (H'.map bergDepth) + 1 = Phi k (H.map bergDepth) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PythagoreanHydra/HydraCalibration.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PythagoreanHydra/HydraCalibration.lean#L46

-- Thm stub generated from Geometry/PythagoreanHydra/HydraCalibration.lean
import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_HydraCalibration
import Definitions.Def_Geometry_PythagoreanHydra_HydraDepth
import Definitions.Def_Geometry_PythagoreanHydra_HydraGame
import Definitions.Def_Geometry_PythagoreanHydra_PythagoreanHydra

/-!
# Calibration of the Pythagorean Hydra: the bound is attained, and descent is necessary

Two complementary results close the analysis of the game.

**Sharpness.**  `exists_maximal_battle` produces, for every hydra `H` of Pythagorean
heads, an actual battle of length exactly `Phi k (H.map bergDepth)`, the upper bound of
`battle_depth_bound`.  Specialised to one head at depth `d` this says the longest battle
has exactly `1 + k + ⋯ + k^d` moves (`single_head_maximal_battle`).  So the length
function of the Pythagorean Hydra is *exactly* the geometric sum — an elementary
function.  There is no room for a Kirby–Paris/Goodstein-style independence phenomenon:
the termination statement comes with a primitive recursive (indeed elementary) witness,
so it is provable by `Σ₁`-induction on the potential.

**Necessity of descent.**  The reason is precisely that inverse Berggren moves go
*down* the tree.  If the regrowth rule is relaxed so that a regrown head may have the
same level (`HydraStepLe`) — let alone a larger one, as happens if the hydra regrows the
Berggren *children* of the chopped head (`BergChopDown`) — then termination fails
outright: `hydraStepLe_has_infinite_play` and `berg_children_infinite_battle` exhibit
explicit infinite plays.  The Pythagorean Hydra therefore sits exactly on the boundary:
strict Berggren descent is both sufficient and necessary for Hercules to win.
-/

open PythHydra

/-! ### Sharpness: the maximal battle -/

theorem PythHydra.berg_step_depth_pred{k : ℕ} {H : Multiset (ℤ × ℤ × ℤ)} (hH : H ≠ 0) :
    ∃ H', BergChop k H H' ∧ Phi k (H'.map bergDepth) + 1 = Phi k (H.map bergDepth) := by sorry
