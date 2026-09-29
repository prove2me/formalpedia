-- Prove2me | Theorems.Thm_TropicalElimination_exists_mem_support_eq_pair
-- name    : TropicalElimination.exists_mem_support_eq_pair
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:39:48.622466+00:00
-- url     : https://prove2.me/theorems/eae7110a-df29-4d58-8501-2039fa8e99af
-- title:
--   Conversely, every two-element subset is the support of a member: the
-- statement:
--   Conversely, every two-element subset is the support of a member: the
--   underlying matroid of a tropical hyperplane with finite coefficients is the
--   uniform matroid `U_{n-1,n}`, whose circuits are exactly the pairs.
--
--   ```lean
--   theorem TropicalElimination.exists_mem_support_eq_pair[DecidableEq E] (c : E → TT) (hc : ∀ i, c i ≠ ⊤)
--       {i j : E} (hij : i ≠ j) :
--       ∃ x ∈ tropVanishing c, supp x = {i, j} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/TropicalLinearSpaceElimination.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/TropicalLinearSpaceElimination.lean#L391

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


omit [Fintype E] [Nonempty E] in

theorem TropicalElimination.exists_mem_support_eq_pair[DecidableEq E] (c : E → TT) (hc : ∀ i, c i ≠ ⊤)
    {i j : E} (hij : i ≠ j) :
    ∃ x ∈ tropVanishing c, supp x = {i, j} := by sorry
