-- Prove2me | Definitions.Def_Tropical_TropicalAlgebra_TropicalFano
-- name    : Tropical_TropicalAlgebra_TropicalFano
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:33:05.27988+00:00
-- url     : https://prove2.me/theorems/ee4d5b1b-9de1-4c6d-9160-de441db922a4
-- title:
--   Aether Catalog definitions — Tropical_TropicalAlgebra_TropicalFano
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.TropicalAlgebra.TropicalFano`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/TropicalAlgebra/TropicalFano.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Fano: Certified Incidence Geometry from Min-Plus Defect Data

This file develops a theory of **tropical incidence structures** where:
- Points and lines are tropical affine functionals in ℝ³
- Incidence is defined by the tropical vanishing condition (minimum attained ≥ 2 times)
- A "defect" measures the gap between the two smallest evaluation values
- Rigidity theorems show the defect profile uniquely determines incidence

## Mathematical Content

In tropical (min-plus) geometry, a tropical polynomial "vanishes" at a point when the
minimum of its terms is achieved at least twice. We formalize this for tropical lines
in the plane (represented as affine functionals `Fin 3 → ℝ`), define the **tropical
defect** as the gap between the smallest and second-smallest evaluation values, and prove:

1. **`tropIncident_iff_defect_eq_zero`**: Incidence ↔ zero defect
2. **`tropDefect_nonneg`**: The defect is always nonneg
3. **`tropDefect_pos_of_not_incident`**: Non-incidence ↔ strictly positive defect
4. **`tropical_fano_rigidity`**: Same defect profile → same incidence relation
5. **`tropical_fano_incidence_reconstructible`**: Under certified separation,
   incidence is exactly the zero set of the defect function

These results establish that the defect matrix of a tropical incidence configuration
is a complete invariant of its incidence relation, providing a bridge from
**certified robustness / vulnerability theory** to **tropical incidence geometry**.

## Cross-Domain Bridges

- **Tropical geometry ↔ Finite projective geometry**: The defect-zero pattern
  can realize Fano-style axioms (3 points per line, unique line through 2 points)
- **Certified ML robustness ↔ Geometric separation**: Security margins become
  tropical non-incidence certificates
- **GL₃ reconstruction ↔ Incidence recovery**: Local defect data determines
  global incidence structure, echoing `reconstruct_from_rank2Levi_profiles_and_edge_moments`
-/

open Finset

noncomputable section

/-- A tropical point in the projective plane, represented as coordinates in ℝ³. -/
def TropPoint := Fin 3 → ℝ

/-- A tropical line in the projective plane, represented as coefficients in ℝ³. -/
def TropLine := Fin 3 → ℝ

/-- Evaluate the tropical affine functional: the i-th term is `ℓ(i) + p(i)`.
    In min-plus convention, this is the i-th "monomial" of the tropical polynomial. -/
def tropEval (ℓ : TropLine) (p : TropPoint) (i : Fin 3) : ℝ :=
  ℓ i + p i

/-- A point lies on a tropical line when the minimum of the evaluation
    is attained at least twice — the **tropical vanishing condition**.

    For three coordinates with values `a, b, c`, this means one of:
    - `a = b` and both are ≤ `c` (minimum attained at indices 0, 1)
    - `a = c` and both are ≤ `b` (minimum attained at indices 0, 2)
    - `b = c` and both are ≤ `a` (minimum attained at indices 1, 2) -/
def tropIncident (ℓ : TropLine) (p : TropPoint) : Prop :=
  let a := tropEval ℓ p 0
  let b := tropEval ℓ p 1
  let c := tropEval ℓ p 2
  (a = b ∧ a ≤ c) ∨ (a = c ∧ a ≤ b) ∨ (b = c ∧ b ≤ a)

/-- The **tropical defect** measures how far a point-line pair is from incidence.

    It equals `median(a, b, c) - min(a, b, c)` where `a, b, c` are the three
    evaluation values. This is zero exactly when the minimum is attained at least
    twice (tropical incidence), and strictly positive otherwise.

    The median of three values is computed as `a + b + c - min - max`. -/
def tropDefect (ℓ : TropLine) (p : TropPoint) : ℝ :=
  let a := tropEval ℓ p 0
  let b := tropEval ℓ p 1
  let c := tropEval ℓ p 2
  let smallest := min a (min b c)
  let largest := max a (max b c)
  (a + b + c - smallest - largest) - smallest

/-
The tropical defect is always nonnegative: the median is ≥ the minimum.
-/

/-
**Core equivalence**: Tropical incidence holds if and only if the defect is zero.

    This is the fundamental theorem connecting the geometric notion of tropical
    vanishing with the quantitative defect measure.
-/


/-- A **certified tropical incidence configuration** packages:
    - a finite set of tropical points and lines,
    - an incidence relation,
    - a proof that incidence agrees with the tropical vanishing condition. -/
structure TropicalIncidenceConfig (P L : Type*) [Fintype P] [Fintype L] where
  /-- Assignment of tropical coordinates to abstract points -/
  point : P → TropPoint
  /-- Assignment of tropical coefficients to abstract lines -/
  line  : L → TropLine
  /-- The abstract incidence relation -/
  Inc   : P → L → Prop
  /-- Incidence agrees with tropical vanishing -/
  inc_spec : ∀ p ℓ, Inc p ℓ ↔ tropIncident (line ℓ) (point p)



/-
**Tropical Fano Rigidity Theorem**: Two tropical incidence configurations
    with the same defect profile have identical incidence relations.

    This is the central rigidity result: the defect matrix is a **complete invariant**
    of the incidence structure. Any two configurations that produce the same
    point-by-line defect values must agree on which points lie on which lines.

    The proof uses `tropIncident_iff_defect_eq_zero` to reduce incidence to the
    zero set of the defect function, then transfers via the defect equality hypothesis.
-/

/-
**Certified Reconstruction Theorem**: Under a certified separation hypothesis
    (every non-incident pair has defect bounded below by a positive margin),
    incidence is exactly characterized by zero defect.

    This theorem formalizes the bridge from **certified robustness** to
    **tropical incidence geometry**: the security margin γ guarantees that
    the incidence relation has no ambiguous cases — every point-line pair
    is either incident (defect = 0) or certified non-incident (defect ≥ γ > 0).
-/

/-! ## Fano-Style Axioms -/

/-- Axioms for a Fano-type incidence structure: 7 points, 7 lines,
    3 points per line, 3 lines per point, unique line through any two
    distinct points, unique intersection of any two distinct lines. -/
structure FanoAxioms {P L : Type*} [Fintype P] [Fintype L] [DecidableEq P] [DecidableEq L]
    (Inc : P → L → Prop) [∀ p ℓ, Decidable (Inc p ℓ)] : Prop where
  /-- There are exactly 7 points -/
  card_points : Fintype.card P = 7
  /-- There are exactly 7 lines -/
  card_lines  : Fintype.card L = 7
  /-- Every line contains exactly 3 points -/
  three_points_per_line : ∀ ℓ, Fintype.card {p // Inc p ℓ} = 3
  /-- Every point lies on exactly 3 lines -/
  three_lines_per_point : ∀ p, Fintype.card {ℓ // Inc p ℓ} = 3
  /-- Any two distinct points determine a unique line -/
  unique_line_through_two_points :
    ∀ p q, p ≠ q → ∃! ℓ, Inc p ℓ ∧ Inc q ℓ
  /-- Any two distinct lines meet in a unique point -/
  unique_point_on_two_lines :
    ∀ ℓ₁ ℓ₂, ℓ₁ ≠ ℓ₂ → ∃! p, Inc p ℓ₁ ∧ Inc p ℓ₂



end


