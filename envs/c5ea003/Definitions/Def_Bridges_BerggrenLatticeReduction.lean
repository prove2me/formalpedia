-- Prove2me | Definitions.Def_Bridges_BerggrenLatticeReduction
-- name    : Bridges_BerggrenLatticeReduction
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-16T20:24:48.749222+00:00
-- url     : https://prove2.me/theorems/f0c31be9-486b-4082-9c4f-1736c4315294
-- title:
--   Aether Catalog definitions — Bridges_BerggrenLatticeReduction
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.BerggrenLatticeReduction`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/BerggrenLatticeReduction.lean by skeleton subtraction
import Mathlib

/-!
# Berggren–Lattice Reduction Duality via Triple-Tree Semimodule Flows

This file establishes a formally verified bridge between three classical worlds:
**primitive Pythagorean triple dynamics** (Berggren tree), **rank-2 lattice reduction**
(Gauss-reduced binary quadratic forms), and **certified short-basis reconstruction**.

## Main Results

1. **`tripleToForm_pos_def`**: The canonical attachment `tripleToForm` from primitive
   Pythagorean triples to binary quadratic forms always produces a positive-definite form.

2. **`berggren_reduced_iff_gauss_reduced`**: A primitive triple is Berggren-reduced
   (odd leg ≤ even leg) if and only if its canonically attached binary quadratic form
   is Gauss-reduced. This is the core *reduction duality*.

3. **`berggren_step_height_decrease`**: Every inverse Berggren step strictly decreases
   the hypotenuse height, establishing well-founded descent toward the root (3,4,5).

4. **`tripleToForm_discriminant_eq`**: The discriminant of the attached form equals
   `-(3c² + 2ab)`, a canonical arithmetic invariant of the triple.

5. **`triple_recoverable_from_form`**: The form attachment is injective—distinct
   primitive triples produce distinct forms, enabling certified reconstruction.

6. **`reduced_form_short_basis_certificate`**: A Berggren-reduced triple yields an
   explicit short-basis certificate for its attached form.

## Mathematical Significance

The Berggren tree is traditionally viewed as an enumeration device for primitive
Pythagorean triples. This formalization reframes it as a **reduction geometry**:
oriented paths in the tree encode discrete gradient flows on a semimodule of
integral Gram data, and the flow is governed by the same inequalities that control
Gauss reduction of binary quadratic forms.

## References

- B. Berggren, *Pytagoreiska trianglar* (1934)
- C. F. Gauss, *Disquisitiones Arithmeticae* (1801), §171–§183
- F. J. M. Barning, *Over pythagorese en bijna-pythagorese driehoeken* (1963)
-/

set_option maxHeartbeats 800000

open Int

/-! ## Section 1: Core Structures -/

/-- A primitive Pythagorean triple `(a, b, c)` with `a² + b² = c²`,
    all legs positive, `gcd(a,b) = 1`, and `a + b` odd (ensuring one leg
    is odd and the other even). -/
structure PrimitiveTriple where
  a : ℤ
  b : ℤ
  c : ℤ
  pos_a : 0 < a
  pos_b : 0 < b
  pos_c : 0 < c
  pyth : a ^ 2 + b ^ 2 = c ^ 2
  coprime_ab : Int.gcd a b = 1
  odd_sum : Odd (a + b)




/-! ## Section 2: Basic Triple Inequalities -/




/-! ## Section 3: The Canonical Form Attachment -/






/-! ## Section 4: Berggren Reducedness and the Main Duality -/



/-
The absolute value of `b - a` is strictly less than `c` for any
    primitive triple. This is the key inequality ensuring `|B| ≤ A`
    in the attached form.
-/

/-
**The Berggren–Gauss Reduction Duality Theorem.**

    A primitive triple is Berggren-reduced if and only if its canonically
    attached binary quadratic form is Gauss-reduced.

    The proof leverages the Pythagorean relation `a² + b² = c²` to show:
    - The form `(c, b−a, c)` always satisfies `|b−a| < c`, hence `|B| ≤ A`.
    - `A = C` holds trivially.
    - The Gauss tie-breaking condition `A = C → B ≥ 0` simplifies to `b ≥ a`.
    - Therefore Gauss-reducedness reduces to `a ≤ b`, which is exactly
      Berggren-reducedness.
-/

/-! ## Section 5: The Root Triple -/




/-! ## Section 6: Berggren Generators -/

/-- The three Berggren generators as indices. -/
inductive BerggrenGen where
  | L | M | R
  deriving DecidableEq




/-! ## Section 7: Berggren Step and Height -/



/-
Every Berggren step (child → parent) strictly decreases the height.
-/



/-! ## Section 8: The Discriminant is Always Negative -/

/-
The discriminant of the attached form is always negative.
-/

/-! ## Section 9: Form Equivalence -/



/-
Form equivalence preserves the discriminant.
-/

/-! ## Section 10: Reconstruction -/

/-
Reconstruction: from the form data `(c, b-a, c)` and the Pythagorean
    relation, we can uniquely recover `a` and `b`.
-/



/-! ## Section 11: Short-Basis Certificates -/


/-
A Berggren-reduced triple yields a short-basis certificate for its
    attached form. The Minkowski bound holds because for the form (c, b-a, c),
    we have 3c² ≤ 4(3c² + 2ab) = 12c² + 8ab, which is equivalent to
    0 ≤ 9c² + 8ab, always true for positive a,b,c.
-/

/-! ## Section 12: Berggren Symmetry -/



/-! ## Section 13: The Hypotenuse is at Least 5 -/

/-
The hypotenuse of any primitive triple is at least 5.
-/

/-! ## Section 14: Composition Theorem -/


/-! ## Section 15: Explicit Examples -/


