-- Prove2me | Theorems.Thm_PythHydra_no_infinite_playU
-- name    : PythHydra.no_infinite_playU
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:40:18.66972+00:00
-- url     : https://prove2.me/theorems/6745e051-fdef-455f-9af9-ce6fdc1e09d1
-- title:
--   Termination in full generality: even with unbounded regrowth, every play of the
-- statement:
--   **Termination in full generality**: even with unbounded regrowth, every play of the
--   Pythagorean Hydra is finite.  (Dershowitz–Manna: the order type is `ω^ω`.)
--
--   ```lean
--   theorem PythHydra.no_infinite_playU(f : ℕ → Multiset ℕ) (hf : ∀ i, HydraStepU (f i) (f (i + 1))) :
--       False := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PythagoreanHydra/HydraGame.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PythagoreanHydra/HydraGame.lean#L244

-- Thm stub generated from Geometry/PythagoreanHydra/HydraGame.lean
import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_HydraGame

/-!
# The abstract hydra game underlying the Pythagorean Hydra

A *hydra* is a finite multiset of heads, each head carrying a natural number *level*.
Hercules chops one head; the hydra regrows an arbitrary finite multiset of new heads,
each of *strictly smaller* level.  In the Pythagorean Hydra of
`Catalog/Geometry/PythagoreanHydra/PythagoreanHydra.lean` the heads are primitive
Pythagorean triples and the regrown heads are Berggren ancestors of the chopped one, so
the level of a head is (a monotone function of) its position in the Berggren tree.

Two regimes are analysed here.

* **Bounded branching** (`HydraStep k`): at most `k` heads regrow.  The potential
  `Phi k H = ∑_{x ∈ H} (1 + k + ⋯ + k^x)` drops by *at least one* at every move
  (`hydraStep_Phi_succ_le`), and there is a strategy realising a drop of *exactly*
  one at every move (`exists_maximal_play`).  Hence the length of the longest play is
  **exactly** `Phi k H` (`longest_play_eq`), an explicit elementary function of the
  initial hydra: `Phi k H ≤ card H * (k+1)^(maxlevel+1)`.  This is the *calibration*
  result: the game is `ω^ω`-style, provably terminating by an explicit primitive
  recursive bound, and therefore has none of the proof-theoretic strength of the
  Kirby–Paris hydra (whose length function majorises every provably total function
  of Peano Arithmetic).

* **Unbounded branching** (`HydraStepU`): arbitrarily many heads may regrow.  Every
  play still terminates (`no_infinite_playU`, via the Dershowitz–Manna order), but the
  length is no longer bounded by any function of the initial hydra alone
  (`unbounded_play_length`), so the game's ordinal is genuinely `> ω`.
-/

open PythHydra

open Multiset

/-! ### The potential function -/













/-! ### The game with bounded branching -/








/-! ### The bound is sharp -/





/-! ### The game with unbounded branching -/

theorem PythHydra.no_infinite_playU(f : ℕ → Multiset ℕ) (hf : ∀ i, HydraStepU (f i) (f (i + 1))) :
    False := by sorry
