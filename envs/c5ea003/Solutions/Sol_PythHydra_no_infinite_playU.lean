-- Prove2me | solution 1 for PythHydra.no_infinite_playU
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:17:54.374995+00:00
-- url     : https://prove2.me/submissions/e4f9eade-20ca-48cf-bca2-5aae7a29732f

-- Sol generated from Geometry/PythagoreanHydra/HydraGame.lean
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


theorem hydraStepU_isDershowitzMannaLT {H H' : Multiset ℕ} (h : HydraStepU H H') :
    Multiset.IsDershowitzMannaLT H' H := by
  obtain ⟨m, H₀, R, hlt⟩ := h
  refine ⟨H₀, R, {m}, by simp, by rw [add_comm], by rw [add_comm, Multiset.singleton_add], ?_⟩
  intro y hy
  exact ⟨m, by simp, hlt y hy⟩






open PythHydra in
theorem solution(f : ℕ → Multiset ℕ) (hf : ∀ i, HydraStepU (f i) (f (i + 1))) :
    False := by
  have wf : WellFounded (Multiset.IsDershowitzMannaLT : Multiset ℕ → Multiset ℕ → Prop) :=
    Multiset.wellFounded_isDershowitzMannaLT
  obtain ⟨a, ⟨i, rfl⟩, hmin⟩ := wf.has_min (Set.range f) ⟨f 0, ⟨0, rfl⟩⟩
  exact hmin (f (i + 1)) ⟨i + 1, rfl⟩ (hydraStepU_isDershowitzMannaLT (hf i))
