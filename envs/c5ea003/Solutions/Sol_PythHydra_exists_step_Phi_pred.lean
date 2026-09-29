-- Prove2me | solution 1 for PythHydra.exists_step_Phi_pred
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:16:20.250808+00:00
-- url     : https://prove2.me/submissions/e90946fd-204d-4d2f-8e67-7596a13e0ee9

-- Sol generated from Geometry/PythagoreanHydra/HydraGame.lean
import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_HydraGame
import Theorems.Thm_PythHydra_Phi_add
import Theorems.Thm_PythHydra_Phi_cons
import Theorems.Thm_PythHydra_Phi_replicate
import Theorems.Thm_PythHydra_phi_succ
import Theorems.Thm_PythHydra_phi_zero

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








open PythHydra in
theorem solution{k : ℕ} {H : Multiset ℕ} (hH : H ≠ 0) :
    ∃ H', HydraStep k H H' ∧ Phi k H' + 1 = Phi k H := by
  obtain ⟨m, hmem⟩ := Multiset.exists_mem_of_ne_zero hH
  obtain ⟨H₀, rfl⟩ := Multiset.exists_cons_of_mem hmem
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨H₀, ?_, ?_⟩
    · have h0 : HydraStep k (0 ::ₘ H₀) (0 + H₀) := HydraStep.chop 0 H₀ 0 (by simp) (by simp)
      simpa using h0
    · simp only [Phi_cons, phi_zero]
      omega
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    refine ⟨Multiset.replicate k m' + H₀, HydraStep.chop _ _ _ ?_ ?_, ?_⟩
    · intro x hx
      have := Multiset.eq_of_mem_replicate hx
      omega
    · simp
    · rw [Phi_add, Phi_cons, Phi_replicate, phi_succ]
      ring
