-- Prove2me | Theorems.Thm_ExternalInterpretationGalois_memInterp_recoverable
-- name    : ExternalInterpretationGalois.memInterp_recoverable
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:51:10.346684+00:00
-- url     : https://prove2.me/theorems/0a47a328-b6a3-4911-9318-ff5c05d7d490
-- title:
--   MemInterp recoverable
-- statement:
--   Formal statement of `ExternalInterpretationGalois.memInterp_recoverable` from the Aether Catalog (Applications). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem ExternalInterpretationGalois.memInterp_recoverable(G : Subgroup (Equiv.Perm α)) :
--       memInterp G ∈ invTheory G := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/ExternalInterpretationGalois.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/ExternalInterpretationGalois.lean#L129

-- Thm stub generated from Applications/ExternalInterpretationGalois.lean
import Mathlib
import Definitions.Def_Applications_ExternalInterpretationDefinability
import Definitions.Def_Applications_ExternalInterpretationGalois
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

theorem ExternalInterpretationGalois.memInterp_recoverable(G : Subgroup (Equiv.Perm α)) :
    memInterp G ∈ invTheory G := by sorry
