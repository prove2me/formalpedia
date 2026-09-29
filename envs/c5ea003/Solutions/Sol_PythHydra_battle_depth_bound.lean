-- Prove2me | solution 1 for PythHydra.battle_depth_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T13:33:26.061185+00:00
-- url     : https://prove2.me/submissions/579a438b-c5a0-490f-9dc4-a4c69653e580

-- Sol generated from Geometry/PythagoreanHydra/HydraDepth.lean
import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_BerggrenAddress
import Definitions.Def_Geometry_PythagoreanHydra_BerggrenDescent
import Definitions.Def_Geometry_PythagoreanHydra_HydraDepth
import Definitions.Def_Geometry_PythagoreanHydra_HydraGame
import Definitions.Def_Geometry_PythagoreanHydra_PythagoreanHydra
import Theorems.Thm_PythHydra_bergDepth_parent
import Theorems.Thm_PythHydra_play_length_le

/-!
# Depth in the Berggren tree, and the sharp form of the Pythagorean Hydra bound

`PythagoreanHydra.lean` measures a head by its hypotenuse.  The *intrinsic* measure is the
depth of the head in the Berggren tree, i.e. the length of its unique address
(`BerggrenAddress.lean`).  Here we

* define `bergDepth` and prove `bergDepth (addr w) = w.length`;
* prove that the inverse Berggren move drops the depth by exactly one
  (`bergDepth_parent`), hence Berggren ancestors have strictly smaller depth;
* re-run the hydra bound with `bergDepth` as the level, obtaining the sharp statement
  `battle_depth_bound : N ≤ Phi k (H.map bergDepth)`;
* deduce that a battle starting at a node of depth `d` with branching bound `k` lasts at
  most `(k+1)^(d+1)` moves, and that a battle starting at the root `(3,4,5)` lasts at
  most **one** move.

This is the exact calibration of the Pythagorean Hydra: its length function is
`(k+1)^(depth+1)`, an elementary function of the address length — nothing like the
`ε₀`-recursive length function of the Kirby–Paris hydra.
-/

open PythHydra





theorem parentStep_depth_lt {s t : ℤ × ℤ × ℤ} (h : ParentStep s t) :
    bergDepth s < bergDepth t := by
  obtain ⟨hppt, hc, rfl⟩ := h
  have := bergDepth_parent hppt hc
  have ht : (t.1, t.2.1, t.2.2) = t := rfl
  rw [ht] at this
  omega

/-- Berggren ancestors sit strictly closer to the root. -/
theorem ancestor_depth_lt {s t : ℤ × ℤ × ℤ} (h : IsBergAncestor s t) :
    bergDepth s < bergDepth t := by
  induction h with
  | single hst => exact parentStep_depth_lt hst
  | tail _ hstep ih => exact lt_trans ih (parentStep_depth_lt hstep)

theorem bergChop_map_depth {k : ℕ} {H H' : Multiset (ℤ × ℤ × ℤ)} (h : BergChop k H H') :
    HydraStep k (H.map bergDepth) (H'.map bergDepth) := by
  obtain ⟨t, H₀, R, hR, hcard⟩ := h
  simp only [Multiset.map_cons, Multiset.map_add]
  refine HydraStep.chop (bergDepth t) (H₀.map bergDepth) (R.map bergDepth) ?_ ?_
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := Multiset.mem_map.mp hx
    exact ancestor_depth_lt (hR s hs)
  · simpa using hcard

theorem battle_to_stepsTo_depth {k : ℕ} : ∀ (N : ℕ) (H H' : Multiset (ℤ × ℤ × ℤ)),
    Battle k N H H' → StepsTo k N (H.map bergDepth) (H'.map bergDepth) := by
  intro N
  induction N with
  | zero => intro H H' h; rw [h]; rfl
  | succ n ih =>
    rintro H H' ⟨M, hstep, hrest⟩
    exact ⟨M.map bergDepth, bergChop_map_depth hstep, ih M H' hrest⟩






open PythHydra in
theorem solution{k N : ℕ} {H H' : Multiset (ℤ × ℤ × ℤ)} (h : Battle k N H H') :
    N ≤ Phi k (H.map bergDepth) :=
  play_length_le (battle_to_stepsTo_depth N H H' h)
