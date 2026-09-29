-- Prove2me | Definitions.Def_Applications_ExternalInterpretationGalois
-- name    : Applications_ExternalInterpretationGalois
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:46:37.788871+00:00
-- url     : https://prove2.me/theorems/52cadfb6-61dd-42a9-a6bf-ba7ab9ba4701
-- title:
--   Aether Catalog definitions — Applications_ExternalInterpretationGalois
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.ExternalInterpretationGalois`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/ExternalInterpretationGalois.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_ExternalInterpretationDefinability
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


namespace ExternalInterpretationGalois

open ExternalInterpretationDefinability

universe u

variable {α : Type u}

/-! ## Configurations and the pointwise action -/

/-- The space of **configurations**: `α`-indexed tuples of elements of `α`.
Interpretations of configurations are the natural test objects for how much a
symmetry group is seen by structural truth. -/
def Config (α : Type u) : Type u := α → α

instance : MulAction (Equiv.Perm α) (Config α) where
  smul σ f := fun a => σ (f a)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl


/-- The identity configuration, i.e. the tuple listing every element of `α` once. -/
def idConfig (α : Type u) : Config α := fun a => a


/-! ## The two sides of the correspondence -/

/-- An **interpretation theory**: a set of propositional interpretations of
configurations. -/
abbrev Theory (α : Type u) : Type u := Set (Config α → Prop)

/-- The theory of a symmetry group: all interpretations recoverable from the
structural truth `G` provides. -/
def invTheory (G : Subgroup (Equiv.Perm α)) : Theory α :=
  {I | Recoverable G I}

/-- A permutation **preserves** an interpretation when it cannot change any
meaning. -/
def Preserves (σ : Equiv.Perm α) (I : Config α → Prop) : Prop :=
  ∀ f : Config α, I (σ • f) = I f

/-- The symmetry group of a theory: all permutations preserving every
interpretation in it.  This is a subgroup. -/
def symGroup (S : Theory α) : Subgroup (Equiv.Perm α) where
  carrier := {σ | ∀ I ∈ S, Preserves σ I}
  one_mem' := by
    intro I _ f
    simp [one_smul]
  mul_mem' := by
    intro σ τ hσ hτ I hI f
    rw [mul_smul, hσ I hI, hτ I hI]
  inv_mem' := by
    intro σ hσ I hI f
    have := hσ I hI (σ⁻¹ • f)
    rw [smul_inv_smul] at this
    exact this.symm


/-! ## Recoverable interpretations of configurations -/



/-- The **membership interpretation** of a subgroup: a configuration is
meaningful exactly when it is (the underlying tuple of) a symmetry in `G`.  This
is the interpretation that detects `G` itself. -/
def memInterp (G : Subgroup (Equiv.Perm α)) : Config α → Prop :=
  fun f => ∃ g : Equiv.Perm α, g ∈ G ∧ (fun a => g a) = f




/-! ## The Galois connection -/







/-! ## A concrete two-element witness -/


end ExternalInterpretationGalois


