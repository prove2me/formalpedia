-- Prove2me | Theorems.Thm_TropicalElimination_mem_tropVanishing_iff_min_attained_twice
-- name    : TropicalElimination.mem_tropVanishing_iff_min_attained_twice
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:39:56.366908+00:00
-- url     : https://prove2.me/theorems/fac101ef-06c1-4ed1-8d63-864c440c3eef
-- title:
--   Over a finite index set, membership in `tropVanishing c` is exactly the
-- statement:
--   Over a finite index set, membership in `tropVanishing c` is exactly the
--   classical tropical vanishing condition: the minimum of `c i + x i` is attained at
--   least twice.
--
--   ```lean
--   theorem TropicalElimination.mem_tropVanishing_iff_min_attained_twice(x : E → TT) :
--       x ∈ tropVanishing c ↔
--         ∃ i j, i ≠ j ∧ (∀ k, c i + x i ≤ c k + x k) ∧ c j + x j = c i + x i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/TropicalLinearSpaceElimination.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/TropicalLinearSpaceElimination.lean#L135

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

theorem TropicalElimination.mem_tropVanishing_iff_min_attained_twice(x : E → TT) :
    x ∈ tropVanishing c ↔
      ∃ i j, i ≠ j ∧ (∀ k, c i + x i ≤ c k + x k) ∧ c j + x j = c i + x i := by sorry
