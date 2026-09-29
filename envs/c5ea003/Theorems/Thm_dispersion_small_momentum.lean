-- Prove2me | Theorems.Thm_dispersion_small_momentum
-- name    : dispersion_small_momentum
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T16:53:58.181643+00:00
-- url     : https://prove2.me/theorems/b5858290-aa55-49bc-8081-a1b40039c174
-- title:
--   Dispersion small momentum
-- statement:
--   Formal statement of `dispersion_small_momentum` from the Aether Catalog (Evergreen). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem dispersion_small_momentum(x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
--       |Real.sin x - x| ≤ x ^ 3 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Evergreen/Pythagorean/PythagoreanPhotonics.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Evergreen/Pythagorean/PythagoreanPhotonics.lean#L267

-- Thm stub generated from Evergreen/Pythagorean/PythagoreanPhotonics.lean
import Mathlib
import Definitions.Def_Evergreen_Pythagorean_PythagoreanPhotonics
/-
# Pythagorean Photonics — Formally Verified Theorems

New theorems connecting Pythagorean triples to discrete spacetime structure,
developed as part of the Pythagorean Photonics research project.

## Main Results

1. **Lattice null vectors**: Integer null vectors on ℤ³ are exactly Pythagorean triples
2. **Pythagorean direction density**: For any rational angle, arbitrarily close
   Pythagorean directions exist
3. **Dispersion bound**: Lattice corrections to the speed of light are quadratically suppressed
4. **Lorentz violation bound**: The anisotropy of a cubic lattice is bounded by (a/λ)²
5. **Berggren tree growth**: The hypotenuse grows at least geometrically in the tree
6. **Quadruple angular coverage**: The number of Pythagorean quadruple directions
   grows at least quadratically
7. **Gaussian integer factorization**: Sum-of-squares multiplicativity (optics connection)
-/


open Finset BigOperators

/-! ## Section 1: Lattice Null Vectors and Discrete Light Cones -/



/-
PROBLEM
A lattice null vector has zero Minkowski norm

PROVIDED SOLUTION
Unfold IsLatticeNull and minkowski3. From h.1 we have a^2 + b^2 = c^2, so a^2 + b^2 - c^2 = 0. Use omega or linarith.
-/

/-
PROBLEM
Negating components preserves the null property

PROVIDED SOLUTION
Unfold IsLatticeNull. neg_sq shows (-a)^2 = a^2, so the Pythagorean equation is preserved. The nonzero condition follows since -a ≠ 0 ↔ a ≠ 0.
-/

/-
PROBLEM
Swapping legs preserves the null property

PROVIDED SOLUTION
Unfold IsLatticeNull. Use add_comm to swap a^2 + b^2 to b^2 + a^2. The nonzero condition: swap the disjunction.
-/

/-
PROBLEM
Scaling preserves the null property

PROVIDED SOLUTION
Unfold IsLatticeNull. (k*a)^2 + (k*b)^2 = k^2*(a^2+b^2) = k^2*c^2 = (k*c)^2 by ring and h.1. For nonzero: if a ≠ 0 then k*a ≠ 0 since k ≠ 0, similarly for b.
-/

/-! ## Section 2: Euclid's Formula and Parametric Families -/

/-
PROBLEM
Every Euclid-parametrized triple is a lattice null vector (when m ≠ n)

PROVIDED SOLUTION
Unfold IsLatticeNull. The Pythagorean equation (m^2-n^2)^2 + (2mn)^2 = (m^2+n^2)^2 follows by ring. For the nonzero condition, m^2 - n^2 = (m-n)(m+n). Since m ≠ n, m-n ≠ 0. Also m+n is nonzero if m and n are not both zero. Actually we just need to show m^2-n^2 ≠ 0 OR 2mn ≠ 0. Since m ≠ n, m^2 ≠ n^2 so m^2 - n^2 ≠ 0. Use sq_left_inj or similar to show m^2 ≠ n^2 from m ≠ n... Actually that's not true in general (could have m = -n). Let me think again. We have m ≠ n. If m^2 = n^2 then m = n or m = -n. Since m ≠ n, we'd need m = -n. Then 2mn = -2n^2. If n ≠ 0, then 2mn ≠ 0. If n = 0, then m = 0 too contradicting m ≠ n... wait m = -n and n = 0 means m = 0 = n, contradiction. So either m^2 - n^2 ≠ 0 or (m = -n and 2mn ≠ 0).
-/

/-
PROBLEM
The Euclid parametrization gives positive hypotenuse when m, n > 0

PROVIDED SOLUTION
m^2 > 0 and n^2 > 0, so m^2 + n^2 > 0. Use positivity or nlinarith [sq_nonneg m, sq_nonneg n, sq_pos_of_pos hm, sq_pos_of_pos hn].
-/

/-
PROBLEM
Euclid's formula: the algebraic identity underlying Pythagorean triples

PROVIDED SOLUTION
Pure algebraic identity. Use ring.
-/

/-! ## Section 3: Berggren Tree Growth Bounds -/

/-
PROBLEM
Under Berggren M₂, the hypotenuse satisfies c' = 2a + 2b + 3c ≥ 3c for a,b > 0

PROVIDED SOLUTION
2*a + 2*b + 3*c > 3*c since a > 0 and b > 0. Use linarith.
-/

/-
PROBLEM
Under any Berggren transformation, the hypotenuse strictly increases
    for positive primitive triples

PROVIDED SOLUTION
We need c < 2a - 2b + 3c, i.e., 2a - 2b + 2c > 0, i.e., a - b + c > 0. Since a^2 + b^2 = c^2, we have c ≥ b (since a > 0), so c - b ≥ 0, and a > 0, hence a + (c-b) > 0. Use nlinarith with h, ha, hb, hc.
-/

/-! ## Section 4: Gaussian Integers and Optical Superposition -/

/-
PROBLEM
The Brahmagupta-Fibonacci identity: sums of squares are multiplicative.
    Physical interpretation: combining two polarization states produces another.

PROVIDED SOLUTION
ring
-/

/-
PROBLEM
Alternative form of Brahmagupta-Fibonacci

PROVIDED SOLUTION
ring
-/

/-
PROBLEM
Product of two Pythagorean hypotenuses gives another sum of squares

PROVIDED SOLUTION
From h1, c^2 = a^2 + b^2. From h2, d^2 = a^2 + b^2. So c^2 * d^2 = (a^2+b^2)^2. Take e = a^2 - b^2 and f = 2*a*b, but actually we need c^2 * d^2 = c^2 * c^2 (since c^2 = d^2)... Wait, h1 says a^2+b^2 = c^2 and h2 says a^2+b^2 = d^2, so c^2 = d^2 and c^2*d^2 = c^4 = (c^2)^2 + 0^2. Use e = c*d, f = 0. Actually c^2*d^2 = (c*d)^2 = (c*d)^2 + 0^2.
-/

/-! ## Section 5: Pythagorean Quadruples and 3D Light Cones -/


/-
PROBLEM
The parametrization always produces a valid quadruple

PROVIDED SOLUTION
Unfold IsPythQuadruple. The goal is a polynomial identity. Use ring.
-/

/-
PROBLEM
Embedding: every Pythagorean triple gives a quadruple

PROVIDED SOLUTION
Unfold IsPythQuadruple. a^2 + b^2 + 0^2 = a^2 + b^2 = c^2 by h. Use simp and h, or nlinarith [sq_nonneg 0].
-/

/-
PROBLEM
Permuting spatial components preserves the quadruple property

PROVIDED SOLUTION
Unfold IsPythQuadruple. b^2 + a^2 + c^2 = a^2 + b^2 + c^2 = d^2. Use linarith or ring_nf with h.
-/

/-
PROBLEM
Permuting spatial components preserves the quadruple property

PROVIDED SOLUTION
Unfold IsPythQuadruple. c^2 + b^2 + a^2 = a^2 + b^2 + c^2 = d^2. Use linarith.
-/

/-
PROBLEM
Scaling quadruples

PROVIDED SOLUTION
Unfold IsPythQuadruple. (ka)^2 + (kb)^2 + (kc)^2 = k^2(a^2+b^2+c^2) = k^2*d^2 = (kd)^2 by ring and h.
-/

/-! ## Section 6: Dispersion Relation Properties -/

/-
PROBLEM
The lattice dispersion correction is negative (energy is always ≤ pc)

PROVIDED SOLUTION
This is sin(x) ≤ x for x = p*a/2 > 0. Use Real.sin_le from Mathlib or sin_le_of_nonneg or similar.
-/

/-
PROBLEM
For small momenta, the lattice dispersion approaches the continuous limit

PROVIDED SOLUTION
Use |sin(x) - x| ≤ |x|^3 / 6 ≤ x^3 for 0 ≤ x ≤ 1. Use Real.abs_sin_sub_self_le or similar Mathlib bound. Or use abs_sin_lt_abs_of_ne_zero and bound carefully.
-/

theorem dispersion_small_momentum(x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    |Real.sin x - x| ≤ x ^ 3 := by sorry
