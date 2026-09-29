-- Prove2me | solution 1 for ToricCode.sum_le_weight_of_both_windings
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T13:53:09.787661+00:00
-- url     : https://prove2.me/submissions/c4f7f7de-1934-4b6b-8646-379de3d03ad3

-- Sol generated from Geometry/ToricCode/ClassWeights.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_ClassWeights
import Definitions.Def_Geometry_ToricCode_Distance
import Definitions.Def_Geometry_ToricCode_Homology
import Theorems.Thm_ToricCode_hWind_const
import Theorems.Thm_ToricCode_support_card_eq
import Theorems.Thm_ToricCode_vWind_const
/-!
# Weights of individual logical classes: the diagonal class costs `M + N`

`ToricCode.toric_distance` says the *minimum* over all logical operators of the
`M × N` torus is `min M N`.  This file refines the analysis to individual
homology classes.

The winding pair `(hWind z 0, vWind z 0) ∈ 𝔽₂²` is a complete invariant of the
homology class (`ToricCode.boundaries_eq_trivialWinding`).  There are therefore
three nonzero classes: "horizontal", "vertical" and "diagonal".  The two cut
families — the `M` column cuts (horizontal edges) and the `N` row cuts (vertical
edges) — are *disjoint* as sets of qubits, so a cycle in the diagonal class must
meet all `M + N` of them:

* `sum_le_weight_of_both_windings` : weight `≥ M + N` for the diagonal class;
* `hammingNorm_loopHV` : the sum of the row loop and the column loop has weight
  exactly `M + N`;
* `diagonal_class_distance` : the minimal weight in the diagonal class is
  exactly `M + N`.

So the logical weight structure of the toric code is *not* uniform across
classes: the distance `min M N` is attained only on an "axis" class, and the
diagonal class is strictly more expensive.
-/

open Matrix

open ToricCode

variable (M N : ℕ) [NeZero M] [NeZero N]












open ToricCode in
theorem solution{z : Edge M N → F2}
    (hz : z ∈ cycles M N) (hh : hWind M N z 0 ≠ 0) (hv : vWind M N z 0 ≠ 0) :
    M + N ≤ hammingNorm z := by
  classical
  have hcyc : (d1 M N) *ᵥ z = 0 := by simpa [cycles, LinearMap.mem_ker] using hz
  have hcard : (Finset.univ : Finset (ZMod M ⊕ ZMod N)).card = M + N := by
    simp [ZMod.card]
  refine le_trans (le_of_eq hcard.symm) ?_
  rw [support_card_eq]
  refine Finset.card_le_card_of_surjOn
    (fun e : Edge M N => if e.1 then Sum.inr e.2.2 else Sum.inl e.2.1) ?_
  rintro (i | j) -
  · have hi : hWind M N z i ≠ 0 := by rw [hWind_const M N hcyc i]; exact hh
    have hex : ∃ y : ZMod N, z (false, (i, y)) ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hi (Finset.sum_eq_zero (fun y _ => hc y))
    obtain ⟨y, hy⟩ := hex
    exact ⟨(false, (i, y)), by simpa using hy, rfl⟩
  · have hj : vWind M N z j ≠ 0 := by rw [vWind_const M N hcyc j]; exact hv
    have hex : ∃ x : ZMod M, z (true, (x, j)) ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hj (Finset.sum_eq_zero (fun x _ => hc x))
    obtain ⟨x, hx⟩ := hex
    exact ⟨(true, (x, j)), by simpa using hx, rfl⟩
