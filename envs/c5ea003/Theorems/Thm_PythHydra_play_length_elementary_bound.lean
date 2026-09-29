-- Prove2me | Theorems.Thm_PythHydra_play_length_elementary_bound
-- name    : PythHydra.play_length_elementary_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:40:48.485143+00:00
-- url     : https://prove2.me/theorems/1fd9b300-238b-471c-947d-789e45e6a965
-- title:
--   The game length is bounded by an explicit elementary function of the initial hydra:
-- statement:
--   The game length is bounded by an explicit elementary function of the initial hydra:
--   if all heads have level at most `L` then every play has at most
--   `card H * (k+1)^(L+1)` moves.
--
--   ```lean
--   theorem PythHydra.play_length_elementary_bound{k N L : ℕ} {H H' : Multiset ℕ}
--       (hL : ∀ x ∈ H, x ≤ L) (h : StepsTo k N H H') :
--       N ≤ Multiset.card H * (k + 1) ^ (L + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PythagoreanHydra/HydraGame.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PythagoreanHydra/HydraGame.lean#L218

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

theorem PythHydra.play_length_elementary_bound{k N L : ℕ} {H H' : Multiset ℕ}
    (hL : ∀ x ∈ H, x ≤ L) (h : StepsTo k N H H') :
    N ≤ Multiset.card H * (k + 1) ^ (L + 1) := by sorry
