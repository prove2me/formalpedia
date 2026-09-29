-- Prove2me | solution 2 for ExternalInterpretationDefinability.finite_recoverable_iff_definable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T14:22:52.079515+00:00
-- url     : https://prove2.me/submissions/c2db72d4-3ecf-4e7a-b1d4-12da5bc5de69

import Mathlib
import Definitions.Def_Applications_ExternalInterpretationDefinability
open ExternalInterpretationDefinability in
theorem solution {G : Type*} {M : Type*} {V : Type*} [Group G] [MulAction G M] [Finite M]
    (I : M → V) :
    Recoverable G I ↔ ∀ v : V, CountGen G M {x | I x = v} := by
  classical
  -- invariant sets are finite unions of orbits, hence countably generated
  have hgen : ∀ s : Set M, InvariantSet G s → CountGen G M s := by
    intro s hs
    have hFin : ∀ F : Finset M, CountGen G M (⋃ x ∈ F, MulAction.orbit G x) := by
      intro F
      refine Finset.induction_on F ?_ ?_
      · simpa using CountGen.empty
      · intro x F _ ih
        rw [Finset.set_biUnion_insert]
        exact CountGen.union (CountGen.orbit x) ih
    have hs_fin : s.Finite := Set.toFinite s
    have heq : s = ⋃ x ∈ hs_fin.toFinset, MulAction.orbit G x := by
      ext y
      simp only [Set.mem_iUnion, Set.Finite.mem_toFinset, exists_prop]
      constructor
      · intro hy
        exact ⟨y, hy, MulAction.mem_orbit_self y⟩
      · rintro ⟨x, hx, ⟨g, rfl⟩⟩
        exact hs g hx
    rw [heq]
    exact hFin _
  -- countably generated sets are invariant
  have hinv : ∀ s : Set M, CountGen G M s → InvariantSet G s := by
    intro s hs
    induction hs with
    | orbit x =>
      rintro g y ⟨h, rfl⟩
      exact ⟨g * h, mul_smul g h x⟩
    | empty => intro g y hy; exact hy
    | compl _ ih =>
      intro g y hy hgy
      apply hy
      have := ih g⁻¹ hgy
      rwa [inv_smul_smul] at this
    | union _ _ ih₁ ih₂ =>
      intro g y hy
      rcases hy with hy | hy
      · exact Or.inl (ih₁ g hy)
      · exact Or.inr (ih₂ g hy)
  constructor
  · -- a recoverable interpretation has invariant fibres
    rintro ⟨F, hF⟩ v
    apply hgen
    intro g x hx
    show I (g • x) = v
    rw [← hF (g • x), ← (hx : I x = v), ← hF x]
    exact congrArg F (Quotient.sound ⟨g, rfl⟩)
  · -- invariant fibres make `I` constant on orbits, so it descends to the quotient
    intro h
    refine ⟨Quotient.lift I ?_, fun x => rfl⟩
    intro a b hab
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hab
    exact hinv _ (h (I b)) g (show I b = I b from rfl)
