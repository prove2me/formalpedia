-- Prove2me | Definitions.Def_Geometry_PythagoreanHydra_HydraGame
-- name    : Geometry_PythagoreanHydra_HydraGame
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:51:49.50613+00:00
-- url     : https://prove2.me/theorems/82915f0e-b24b-48f8-b08b-eb3702b7ad43
-- title:
--   Aether Catalog definitions — Geometry_PythagoreanHydra_HydraGame
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.PythagoreanHydra.HydraGame`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/PythagoreanHydra/HydraGame.lean by skeleton subtraction
import Mathlib

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

namespace PythHydra

open Multiset

/-! ### The potential function -/

/-- `phi k n = 1 + k + k² + ⋯ + kⁿ`, the potential of a single head of level `n`
in a hydra with branching bound `k`. -/
def phi (k n : ℕ) : ℕ := ∑ i ∈ Finset.range (n + 1), k ^ i






/-- The potential of a whole hydra. -/
def Phi (k : ℕ) (H : Multiset ℕ) : ℕ := (H.map (phi k)).sum






/-! ### The game with bounded branching -/

/-- One move of the hydra game with branching bound `k`: a head of level `m` is chopped
and at most `k` heads of strictly smaller level regrow. -/
inductive HydraStep (k : ℕ) : Multiset ℕ → Multiset ℕ → Prop
  | chop (m : ℕ) (H R : Multiset ℕ) (hlt : ∀ x ∈ R, x < m) (hcard : Multiset.card R ≤ k) :
      HydraStep k (m ::ₘ H) (R + H)


/-- `StepsTo k N H H'` : there is a play of exactly `N` moves from `H` to `H'`. -/
def StepsTo (k : ℕ) : ℕ → Multiset ℕ → Multiset ℕ → Prop
  | 0, H, H' => H = H'
  | (n + 1), H, H' => ∃ M, HydraStep k H M ∧ StepsTo k n M H'





/-! ### The bound is sharp -/





/-! ### The game with unbounded branching -/

/-- One move of the hydra game with *unbounded* regrowth. -/
inductive HydraStepU : Multiset ℕ → Multiset ℕ → Prop
  | chop (m : ℕ) (H R : Multiset ℕ) (hlt : ∀ x ∈ R, x < m) : HydraStepU (m ::ₘ H) (R + H)



/-- Plays in the unbounded game. -/
def StepsToU : ℕ → Multiset ℕ → Multiset ℕ → Prop
  | 0, H, H' => H = H'
  | (n + 1), H, H' => ∃ M, HydraStepU H M ∧ StepsToU n M H'



end PythHydra


