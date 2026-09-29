-- Prove2me | solution 1 for ExternalInterpretationGalois.memInterp_recoverable
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:09:15.578984+00:00
-- url     : https://prove2.me/submissions/af521508-34d7-4b7e-8724-832cee8fc181

-- Sol generated from Applications/ExternalInterpretationGalois.lean
import Mathlib
import Definitions.Def_Applications_ExternalInterpretationDefinability
import Definitions.Def_Applications_ExternalInterpretationGalois
import Theorems.Thm_ExternalInterpretationDefinability_recoverable_iff_orbitConstant
/-
# A Galois Correspondence Between Symmetry Groups and Interpretation Theories

The companion files show that an external interpretation `I : M → V` descends to
structural truth exactly when it is constant on the orbits of the symmetry group
`G` (`ExternalInterpretationDefinability.recoverable_iff_orbitConstant`).  That
result takes the group as given.  This file asks the *inverse* question:

> How much of the symmetry group is visible in the collection of interpretations
> it makes recoverable?

The answer is: **all of it**, provided the interpretations are allowed to speak
about *configurations* (tuples of elements) rather than single points.  Writing
`Config α = α → α` for the space of `α`-indexed configurations, with a
permutation acting pointwise on values, we prove

* `mem_iff_preserves_recoverable` — a permutation `σ` lies in `G` **iff** it
  preserves every `G`-recoverable interpretation of configurations.  This is a
  Krasner-style closure theorem for permutation groups: no proper overgroup and
  no proper subgroup can have the same recoverable theory.
* `invTheory_injective` — hence `G ↦ (its recoverable theory)` is injective, so
  the lattice of symmetry groups embeds into the lattice of interpretation
  theories, antitonically (`invTheory_antitone`, `symGroup_antitone`).
* `symGroup_invTheory` / `invTheory_symGroup_invTheory` — the pair
  (`symGroup`, `invTheory`) is a Galois connection whose group-side closure
  operator is the identity: symmetry groups are exactly the Galois-closed
  objects.
* `invTheory_lt_of_lt` — strict inclusions of groups give strict inclusions of
  theories, and `bool_theories_ne` is a concrete two-element witness.

The moral for the definability programme: "structural truth" determines its own
symmetry group, so the recoverability boundary studied in the other files is an
intrinsic invariant of the theory, not an artefact of the chosen group
presentation.
-/


open ExternalInterpretationGalois

open ExternalInterpretationDefinability

universe u

variable {α : Type u}

/-! ## Configurations and the pointwise action -/






/-! ## The two sides of the correspondence -/






/-! ## Recoverable interpretations of configurations -/

/-- Membership in a group's theory, unfolded to orbit constancy. -/
lemma mem_invTheory_iff {G : Subgroup (Equiv.Perm α)} {I : Config α → Prop} :
    I ∈ invTheory G ↔ ∀ (g : G) (f : Config α), I (g • f) = I f := by
  constructor
  · intro hI g f
    have h := (recoverable_iff_orbitConstant (G := G) I).mp hI (⟨g, rfl⟩ : Indist G f (g • f))
    exact propext ⟨fun hx => h ▸ hx, fun hx => h ▸ hx⟩
  · intro h
    refine (recoverable_iff_orbitConstant (G := G) I).mpr ?_
    rintro x y ⟨g, rfl⟩
    exact (h g x).symm






/-! ## The Galois connection -/







/-! ## A concrete two-element witness -/



open ExternalInterpretationGalois in
theorem solution(G : Subgroup (Equiv.Perm α)) :
    memInterp G ∈ invTheory G := by
  refine mem_invTheory_iff.mpr ?_
  rintro ⟨σ, hσ⟩ f
  refine propext ⟨?_, ?_⟩
  · rintro ⟨g, hg, hgf⟩
    refine ⟨σ⁻¹ * g, G.mul_mem (G.inv_mem hσ) hg, ?_⟩
    funext a
    have h1 : g a = σ (f a) := congrArg (fun h => h a) hgf
    simp [Equiv.Perm.coe_mul, h1]
  · rintro ⟨g, hg, hgf⟩
    refine ⟨σ * g, G.mul_mem hσ hg, ?_⟩
    funext a
    have h1 : g a = f a := congrArg (fun h => h a) hgf
    show σ (g a) = σ (f a)
    rw [h1]
