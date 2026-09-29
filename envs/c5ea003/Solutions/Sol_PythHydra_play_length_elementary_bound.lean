-- Prove2me | solution 1 for PythHydra.play_length_elementary_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:19:52.540538+00:00
-- url     : https://prove2.me/submissions/9d662076-197c-4c1f-aaa8-0d5e0871b9b4

-- Sol generated from Geometry/PythagoreanHydra/HydraGame.lean
import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_HydraGame
import Theorems.Thm_PythHydra_phi_le_pow
import Theorems.Thm_PythHydra_play_length_le

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





theorem phi_mono (k : ℕ) {m n : ℕ} (h : m ≤ n) : phi k m ≤ phi k n := by
  have hsub : Finset.range (m + 1) ⊆ Finset.range (n + 1) := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  exact Finset.sum_le_sum_of_subset hsub







/-- If every head of `H` has level at most `m` then `Phi k H ≤ card H * phi k m`. -/
theorem Phi_le_of_forall_le {k m : ℕ} {H : Multiset ℕ} (h : ∀ x ∈ H, x ≤ m) :
    Phi k H ≤ Multiset.card H * phi k m := by
  have : ∀ y ∈ H.map (phi k), y ≤ phi k m := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
    exact phi_mono k (h x hx)
  have hsum := Multiset.sum_le_card_nsmul _ _ this
  simpa [Phi, smul_eq_mul] using hsum

/-! ### The game with bounded branching -/








/-! ### The bound is sharp -/





/-! ### The game with unbounded branching -/








open PythHydra in
theorem solution{k N L : ℕ} {H H' : Multiset ℕ}
    (hL : ∀ x ∈ H, x ≤ L) (h : StepsTo k N H H') :
    N ≤ Multiset.card H * (k + 1) ^ (L + 1) := by
  have h1 := play_length_le h
  have h2 : Phi k H ≤ Multiset.card H * phi k L := Phi_le_of_forall_le hL
  have h3 : phi k L ≤ (k + 1) ^ (L + 1) := phi_le_pow k L
  calc N ≤ Phi k H := h1
    _ ≤ Multiset.card H * phi k L := h2
    _ ≤ Multiset.card H * (k + 1) ^ (L + 1) := Nat.mul_le_mul_left _ h3
