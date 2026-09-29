-- Prove2me | Theorems.Thm_TropicalElimination_tropVanishing_eq_of_unique_min_aux
-- name    : TropicalElimination.tropVanishing_eq_of_unique_min_aux
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:39:55.14793+00:00
-- url     : https://prove2.me/theorems/f5b43b63-cd57-450d-8423-dd36674a965b
-- title:
--   Rigidity lemma (ordered version).
-- statement:
--   **Rigidity lemma** (ordered version).  Suppose the tropical sum of two
--   members of a tropical hyperplane, with the coordinate `e` deleted, has a
--   *strictly* unique minimal coordinate `i₀`.  Then the two members already agree at
--   `i₀`.  This is the combinatorial heart of the elimination theorem: the forced
--   part of the eliminated vector can never have a lonely minimum at a coordinate
--   where the two inputs differ.
--
--   ```lean
--   theorem TropicalElimination.tropVanishing_eq_of_unique_min_aux(c : E → TT) {x y : E → TT}
--       (hx : x ∈ tropVanishing c) (hy : y ∈ tropVanishing c) {e i₀ : E}
--       (hi₀e : i₀ ≠ e) (hxye : x e = y e)
--       (hmin : ∀ j, j ≠ i₀ →
--         c i₀ + min (x i₀) (y i₀) < c j + (if j = e then ⊤ else min (x j) (y j)))
--       (hle : x i₀ ≤ y i₀) : x i₀ = y i₀ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/TropicalLinearSpaceElimination.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/TropicalLinearSpaceElimination.lean#L162

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

omit [Fintype E] [Nontrivial E] in

theorem TropicalElimination.tropVanishing_eq_of_unique_min_aux(c : E → TT) {x y : E → TT}
    (hx : x ∈ tropVanishing c) (hy : y ∈ tropVanishing c) {e i₀ : E}
    (hi₀e : i₀ ≠ e) (hxye : x e = y e)
    (hmin : ∀ j, j ≠ i₀ →
      c i₀ + min (x i₀) (y i₀) < c j + (if j = e then ⊤ else min (x j) (y j)))
    (hle : x i₀ ≤ y i₀) : x i₀ = y i₀ := by sorry
