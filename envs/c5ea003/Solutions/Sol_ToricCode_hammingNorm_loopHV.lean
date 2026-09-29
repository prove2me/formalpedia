-- Prove2me | solution 1 for ToricCode.hammingNorm_loopHV
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T12:52:10.701869+00:00
-- url     : https://prove2.me/submissions/213c62e6-21de-42cb-93cc-944afc2319da

-- Sol generated from Geometry/ToricCode/ClassWeights.lean
import Mathlib
import Definitions.Def_Geometry_ToricCode_Basic
import Definitions.Def_Geometry_ToricCode_ClassWeights
import Definitions.Def_Geometry_ToricCode_Distance
import Theorems.Thm_ToricCode_support_card_eq
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
theorem solution: hammingNorm (loopHV M N) = M + N := by
  classical
  rw [support_card_eq]
  set F : ZMod M ⊕ ZMod N → Edge M N :=
    Sum.elim (fun x => ((false, (x, 0)) : Edge M N)) (fun y => ((true, (0, y)) : Edge M N))
      with hF
  have hinj : Function.Injective F := by
    rintro (a | a) (b | b) h <;> simp [hF] at h ⊢ <;> simp_all
  have hmem : ∀ b : Bool, ∀ (x : ZMod M) (y : ZMod N),
      loopHV M N (b, (x, y)) ≠ 0 ↔ (b = false ∧ y = 0) ∨ (b = true ∧ x = 0) := by
    intro b x y
    cases b
    · simp only [loopHV, Pi.add_apply, loopH, loopV]
      by_cases hy : y = 0 <;> simp [hy]
    · simp only [loopHV, Pi.add_apply, loopH, loopV]
      by_cases hx : x = 0 <;> simp [hx]
  have himg : (Finset.univ.filter (fun e : Edge M N => loopHV M N e ≠ 0))
      = Finset.univ.image F := by
    ext e
    obtain ⟨b, x, y⟩ := e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    rw [hmem]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨Sum.inl x, by simp [hF]⟩
      · exact ⟨Sum.inr y, by simp [hF]⟩
    · rintro ⟨s, hs⟩
      cases s with
      | inl a =>
        left
        simp only [hF, Sum.elim_inl, Prod.mk.injEq] at hs
        exact ⟨hs.1.symm, hs.2.2.symm⟩
      | inr a =>
        right
        simp only [hF, Sum.elim_inr, Prod.mk.injEq] at hs
        exact ⟨hs.1.symm, hs.2.1.symm⟩
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  simp [ZMod.card]
