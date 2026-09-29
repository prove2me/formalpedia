-- Prove2me | Definitions.Def_Tropical_TropicalLinearSpaceElimination
-- name    : Tropical_TropicalLinearSpaceElimination
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:33:16.519095+00:00
-- url     : https://prove2.me/theorems/91c48cca-0701-4e62-9084-6d09adc76d1b
-- title:
--   Aether Catalog definitions — Tropical_TropicalLinearSpaceElimination
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.TropicalLinearSpaceElimination`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/TropicalLinearSpaceElimination.lean by skeleton subtraction
import Mathlib

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

namespace TropicalElimination

/-- The min-plus tropical semiring carrier: rationals with `⊤` as tropical zero. -/
abbrev TT := WithTop ℚ

variable {E : Type*}

/-- Tropical (coordinatewise) addition of vectors: pointwise minimum. -/
def tropAdd (x y : E → TT) : E → TT := fun i => min (x i) (y i)

/-- Tropical scalar multiplication: pointwise addition of a constant. -/
def tropSMul (a : TT) (x : E → TT) : E → TT := fun i => a + x i

/-- The tropical zero vector, all coordinates `⊤`. -/
def tropZero (E : Type*) : E → TT := fun _ => ⊤

/-- A set of tropical vectors that is a subsemimodule: it contains the tropical
zero and is closed under tropical addition and tropical scaling. -/
structure IsTropSemimodule (V : Set (E → TT)) : Prop where
  zero_mem : tropZero E ∈ V
  add_mem : ∀ {x y}, x ∈ V → y ∈ V → tropAdd x y ∈ V
  smul_mem : ∀ (a : TT) {x}, x ∈ V → tropSMul a x ∈ V

/-- The valuated-matroid **vector elimination axiom**: given two members agreeing
at a coordinate `e` where they are both nonzero, some member is `⊤` at `e`,
dominates their tropical sum, and is *equal* to the tropical sum at every
coordinate where the two differ. -/
def SatisfiesElimination (V : Set (E → TT)) : Prop :=
  ∀ x ∈ V, ∀ y ∈ V, ∀ e : E, x e = y e → x e ≠ ⊤ →
    ∃ z ∈ V, z e = ⊤ ∧ (∀ i, min (x i) (y i) ≤ z i) ∧
      ∀ i, x i ≠ y i → z i = min (x i) (y i)

/-- A tropical linear space: a subsemimodule of tropical vectors satisfying the
vector elimination axiom. -/
structure IsTropicalLinearSpace (V : Set (E → TT)) : Prop where
  semimodule : IsTropSemimodule V
  elimination : SatisfiesElimination V

/-- The tropical hyperplane attached to a coefficient vector `c`: the set of
tropical vectors `x` such that for each coordinate `i` some other coordinate `j`
has value at most that of `i`.  Over a finite index set this says exactly that
the minimum of `c i + x i` is attained at least twice. -/
def tropVanishing (c : E → TT) : Set (E → TT) :=
  {x | ∀ i, ∃ j, j ≠ i ∧ c j + x j ≤ c i + x i}

/-- The support of a tropical vector: the coordinates that are not tropically
zero. -/
def supp (x : E → TT) : Set E := {i | x i ≠ ⊤}

section Semimodule

variable [Nontrivial E] (c : E → TT)





end Semimodule

section Characterisation

variable [Fintype E] [Nonempty E] (c : E → TT)


end Characterisation

section Elimination

variable [Fintype E] [DecidableEq E] [Nontrivial E]





end Elimination

section Matroid

variable {V : Set (E → TT)}


variable [Fintype E] [Nonempty E]



end Matroid

end TropicalElimination


