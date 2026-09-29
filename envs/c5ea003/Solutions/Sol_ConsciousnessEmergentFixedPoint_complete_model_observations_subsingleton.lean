-- Prove2me | solution 1 for ConsciousnessEmergentFixedPoint.complete_model_observations_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:16:44.458054+00:00
-- url     : https://prove2.me/submissions/87e5a8a6-f66e-4d45-b75a-8f203057c0f6

-- Sol generated from Bridges/ConsciousnessEmergentFixedPoint/FixedPointBridge.lean
import Mathlib
import Definitions.Def_Bridges_ConsciousnessEmergentFixedPoint_FixedPointBridge

/-!
# Consciousness as an Emergent Fixed Point

A self-model is represented by an interpretation map `A → (A → B)`.  Pointwise
completeness says that every `B`-valued behaviour is represented by a state.
Lawvere's diagonal argument then produces a fixed point for every endomorphism
of `B`.  The representing state supplies a literal closed self-observation loop.

The final section records a type-theoretic form of Yoneda faithfulness:
precomposition by a map is completely determined by its action on the identity.
This connects the exponential object `A → B` used by the self-model to the
representable functor of `A`.
-/

open Function

open ConsciousnessEmergentFixedPoint

universe u v w





/-- Lawvere's diagonal theorem in the Cartesian closed category of types:
a complete self-model produces a strange-loop witness for every observation
transformer. -/
theorem lawvere_strange_loop {A : Type u} {B : Type v}
    (M : SelfModel A B) (hM : M.Complete) (g : B → B) :
    ∃ a : A, M.IsStrangeLoop g a := by
  obtain ⟨a, ha⟩ := hM (fun x => g (M.diagonal x))
  refine ⟨a, ha, ?_⟩
  exact congrFun ha.symm a

/-- Every endomorphism of the observation type has a fixed point whenever a
complete self-model exists. -/
theorem every_endomorphism_has_fixedPoint {A : Type u} {B : Type v}
    (M : SelfModel A B) (hM : M.Complete) (g : B → B) :
    ∃ b : B, g b = b := by
  obtain ⟨a, _, ha⟩ := lawvere_strange_loop M hM g
  exact ⟨M.diagonal a, ha⟩

/-- A fixed-point-free observation transformer obstructs complete
self-modeling.  This is the Cantor--Lawvere negative half of the bridge. -/
theorem no_complete_model_of_fixedPointFree {A : Type u} {B : Type v}
    (g : B → B) (hg : ∀ b, g b ≠ b) (M : SelfModel A B) :
    ¬ M.Complete := by
  intro hM
  obtain ⟨b, hb⟩ := every_endomorphism_has_fixedPoint M hM g
  exact hg b hb

















open ConsciousnessEmergentFixedPoint in
theorem solution{A : Type u} {B : Type v}
    (M : SelfModel A B) (hM : M.Complete) : Subsingleton B := by
  classical
  constructor
  intro x y
  by_contra hxy
  let g : B → B := fun z => if z = x then y else x
  have hg : ∀ z, g z ≠ z := by
    intro z
    simp only [g]
    split_ifs with hz
    · subst z
      exact fun hyx => hxy hyx.symm
    · intro hxz
      exact hz hxz.symm
  exact no_complete_model_of_fixedPointFree g hg M hM
