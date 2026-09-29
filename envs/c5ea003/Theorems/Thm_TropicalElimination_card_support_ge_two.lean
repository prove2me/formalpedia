-- Prove2me | Theorems.Thm_TropicalElimination_card_support_ge_two
-- name    : TropicalElimination.card_support_ge_two
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:39:46.560256+00:00
-- url     : https://prove2.me/theorems/ac29384f-644b-4124-818c-1c11a85529ac
-- title:
--   In a tropical hyperplane with everywhere-finite coefficients, every nonzero
-- statement:
--   In a tropical hyperplane with everywhere-finite coefficients, every nonzero
--   member has at least two support coordinates: the underlying matroid has no
--   loops.
--
--   ```lean
--   theorem TropicalElimination.card_support_ge_two(c : E → TT) (hc : ∀ i, c i ≠ ⊤) {x : E → TT}
--       (hx : x ∈ tropVanishing c) (hx0 : x ≠ tropZero E) :
--       ∃ i j, i ≠ j ∧ x i ≠ ⊤ ∧ x j ≠ ⊤ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/TropicalLinearSpaceElimination.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/TropicalLinearSpaceElimination.lean#L366

-- Thm stub generated from Tropical/TropicalLinearSpaceElimination.lean
import Mathlib
import Definitions.Def_Tropical_TropicalLinearSpaceElimination

/-!
# Tropical linear spaces: the vector elimination axiom

This file develops the structural core of *tropical ideal* theory in the sense of
Maclagan–Rincón: a tropical ideal is a subsemimodule of the tropical polynomial
semiring which, in each degree, is the set of vectors of a valuated matroid, i.e.
satisfies the **vector elimination axiom**.  The previous catalog file
`Catalog/Tropical/GroebnerBases.lean` treated tropical ideals purely as
`Submodule`s (tropical linear combinations only).  Here we add the missing
matroidal layer and prove that a genuinely interesting semimodule — the set of
tropical vectors *vanishing* against a fixed coefficient vector, i.e. the
tropical hyperplane — satisfies elimination.

Main results:

* `tropVanishing_isTropSemimodule` : tropical hyperplanes are subsemimodules.
* `mem_tropVanishing_iff_min_attained_twice` : the relational definition used
  here agrees with "the minimum is attained at least twice".
* `tropVanishing_elimination` : **the vector elimination axiom holds for every
  tropical hyperplane**.  This is the main theorem; the proof is a genuine
  two-case argument resting on a nontrivial rigidity lemma
  (`tropVanishing_eq_of_unique_min`).
* `tropVanishing_isTropicalLinearSpace` : consequently a tropical hyperplane is a
  tropical linear space.
* `support_elimination` : elimination plus tropical scaling yields the matroid
  (Minty) vector elimination property on supports — a bridge from tropical
  algebra to matroid combinatorics.
* `card_support_ge_two` and `exists_mem_support_eq_pair` : the underlying matroid
  of a tropical hyperplane with finite coefficients is the uniform matroid: the
  minimal supports are exactly the two-element subsets.
-/

open TropicalElimination


variable {E : Type*}










variable [Nontrivial E] (c : E → TT)







variable [Fintype E] [Nonempty E] (c : E → TT)




variable [Fintype E] [DecidableEq E] [Nontrivial E]







variable {V : Set (E → TT)}


variable [Fintype E] [Nonempty E]

theorem TropicalElimination.card_support_ge_two(c : E → TT) (hc : ∀ i, c i ≠ ⊤) {x : E → TT}
    (hx : x ∈ tropVanishing c) (hx0 : x ≠ tropZero E) :
    ∃ i j, i ≠ j ∧ x i ≠ ⊤ ∧ x j ≠ ⊤ := by sorry
