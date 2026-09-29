-- Prove2me | solution 1 for PythHydra.play_length_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:16:19.778098+00:00
-- url     : https://prove2.me/submissions/21ffb83a-d0c9-41c4-8616-58a6ebedefbb

-- Sol generated from Geometry/PythagoreanHydra/HydraGame.lean
import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_HydraGame
import Theorems.Thm_PythHydra_hydraStep_Phi_succ_le

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




/-- The potential bounds the length of every play. -/
theorem stepsTo_Phi_le {k : ℕ} : ∀ (N : ℕ) (H H' : Multiset ℕ),
    StepsTo k N H H' → N + Phi k H' ≤ Phi k H := by
  intro N
  induction N with
  | zero => intro H H' h; subst h; simp
  | succ n ih =>
    rintro H H' ⟨M, hstep, hrest⟩
    have h1 := ih M H' hrest
    have h2 := hydraStep_Phi_succ_le hstep
    omega




/-! ### The bound is sharp -/





/-! ### The game with unbounded branching -/








open PythHydra in
theorem solution{k N : ℕ} {H H' : Multiset ℕ} (h : StepsTo k N H H') :
    N ≤ Phi k H := by
  have := stepsTo_Phi_le N H H' h
  omega
