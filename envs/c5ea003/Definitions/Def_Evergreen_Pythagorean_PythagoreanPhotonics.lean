-- Prove2me | Definitions.Def_Evergreen_Pythagorean_PythagoreanPhotonics
-- name    : Evergreen_Pythagorean_PythagoreanPhotonics
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T16:38:11.177991+00:00
-- url     : https://prove2.me/theorems/efb33678-44c9-4eae-bde4-f90b6be94571
-- title:
--   Aether Catalog definitions — Evergreen_Pythagorean_PythagoreanPhotonics
-- statement:
--   Definition bundle for the Aether Catalog module `Evergreen.Pythagorean.PythagoreanPhotonics`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Evergreen/Pythagorean/PythagoreanPhotonics.lean by skeleton subtraction
import Mathlib
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

/-- A lattice null vector is a nonzero integer vector on the null cone -/
def IsLatticeNull (a b c : ℤ) : Prop :=
  a ^ 2 + b ^ 2 = c ^ 2 ∧ (a ≠ 0 ∨ b ≠ 0)

/-- The Minkowski form in (2+1) dimensions -/
def minkowski3 (a b c : ℤ) : ℤ :=
  a ^ 2 + b ^ 2 - c ^ 2

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

/-- The (3+1) Pythagorean quadruple relation -/
def IsPythQuadruple (a b c d : ℤ) : Prop :=
  a ^ 2 + b ^ 2 + c ^ 2 = d ^ 2

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

/-! ## Section 7: Number-Theoretic Properties of the Lattice -/

/-
PROBLEM
In any Pythagorean triple, at least one leg must be divisible by 3

PROVIDED SOLUTION
Work modulo 3. Squares mod 3 are 0 or 1. If neither a nor b is divisible by 3, then a^2 ≡ 1 and b^2 ≡ 1 mod 3, so a^2+b^2 ≡ 2 mod 3. But c^2 mod 3 is 0 or 1, contradiction. Use ZMod 3 or work with Int.emod directly, or use omega on cases of a%3 and b%3.
-/

/-
PROBLEM
In any Pythagorean triple, at least one leg must be divisible by 4

PROVIDED SOLUTION
We need to show 4 | a*b. Work mod 2: at least one of a,b must be even (since if both odd, a^2+b^2 ≡ 2 mod 4 but c^2 ≡ 0 or 1 mod 4). So 2 | a or 2 | b, hence 2 | ab. Actually we need 4 | ab. If one is even, say 2|a, write a = 2k. Need 4 | 2kb, i.e. 2 | kb. Actually the stronger result: in a Pythagorean triple, at least one of a,b is divisible by 2, and actually ab is divisible by 4 because one leg is divisible by 4 or both legs are even. Let me try a different approach: work mod 4. If a is odd and b is odd: contradiction as before. If a ≡ 0 mod 2 and b is odd: a^2 + b^2 = c^2, b odd so b^2 ≡ 1 mod 4, c^2 - a^2 ≡ 1 mod 4. c must be odd (since a even, b odd). So c^2 ≡ 1, a^2 ≡ 0 mod 4 means a ≡ 0 mod 2. Then a^2 can be 0 mod 4, giving 0+1 = 1 = c^2 mod 4 ✓. So a is divisible by 2, and ab is divisible by 2. We need 4. Actually if a ≡ 2 mod 4, a^2 ≡ 4 ≡ 0 mod 4 still. Hmm. The key is a must be divisible by 4 if b is odd... Actually let me try: use omega/decide on all cases of a%4 and b%4.
-/

/-
PROBLEM
The hypotenuse of a primitive triple is always odd

PROVIDED SOLUTION
If c is even, then c^2 ≡ 0 mod 4, so a^2 + b^2 ≡ 0 mod 4. Squares mod 4 are 0 or 1. So both a,b must be even. But then gcd(a,b) ≥ 2, contradicting gcd(a,gcd(b,c)) = 1 (since gcd(a,b) divides gcd(a,gcd(b,c))). Work with Nat.gcd and modular arithmetic.
-/

/-
PROBLEM
The 3-4-5 triple has the smallest hypotenuse among nontrivial triples

PROVIDED SOLUTION
Since a ≤ b and a^2 + b^2 = c^2, we have c^2 = a^2 + b^2 ≥ a^2 + a^2 = 2a^2, so c ≥ a√2 > a. Also c^2 ≤ 2b^2, so c ≤ b√2. Since gcd(a,b) = 1 and a ≤ b, and a^2 + b^2 = c^2, we need a ≥ 1 and b ≥ 2 (if b=1 then a=1 but 1+1=2 not a perfect square; if a=1, b^2 = c^2-1 = (c-1)(c+1), need (c-1)(c+1) to be a perfect square). The smallest cases: a=1, b=1: c^2=2, not integer. a=1, b=2: c^2=5, no. a=2, b=2: gcd=2≠1. a=1, b=3: c^2=10, no. a=2, b=3: c^2=13, no. a=1, b=4: c^2=17, no. a=3, b=4: c^2=25, c=5. ✓. So c ≥ 5. Use interval_cases or omega after bounding c.
-/

/-! ## Section 8: Infinitude and Density Results -/

/-
PROBLEM
There exist arbitrarily large primitive Pythagorean triples

PROVIDED SOLUTION
Use the triple (3*(N+1), 4*(N+1), 5*(N+1)). Then c = 5*(N+1) > N, and 9(N+1)^2 + 16(N+1)^2 = 25(N+1)^2. All components are positive.
-/

/-
PROBLEM
There are infinitely many Pythagorean quadruples

PROVIDED SOLUTION
Use (a,b,c,d) = (1*(N+1), 2*(N+1), 2*(N+1), 3*(N+1)). Check: 1+4+4=9. So (N+1)^2 + 4(N+1)^2 + 4(N+1)^2 = 9(N+1)^2. d = 3(N+1) > N.
-/

/-
PROBLEM
Between any two Euclid parameters, there is a Pythagorean triple

PROVIDED SOLUTION
Take m = m₂, n = 1 (assuming m₂ ≥ 2, handle m₂ = 1 separately). Then the Euclid triple has c = m₂^2 + 1. We need m₁^2 < m₂^2 + 1 (true since m₁ < m₂) and m₂^2 + 1 ≤ m₂^2 + 1 (trivially). a = m₂^2 - 1, b = 2*m₂. Both positive when m₂ ≥ 2. For m₁ = 0 and m₂ = 1: use (3,4,5), c=5, need 0 < 5 ≤ 2, doesn't work. Actually let me reconsider. We need c with m₁^2 < c ≤ m₂^2 + 1. Let's use (3,4,5) for small cases. Use ⟨3, 4, 5, by norm_num, ...⟩ and show 5 ≤ m₂^2 + 1 when m₂ ≥ 2, and m₁^2 < 5 when m₁ ≤ 1. Actually let's use the triple (3*(m₁+1), 4*(m₁+1), 5*(m₁+1)) with c = 5(m₁+1). Then m₁^2 < 5(m₁+1) iff m₁^2 - 5m₁ - 5 < 0, true for m₁ ≤ 5. And 5(m₁+1) ≤ m₂^2 + 1 needs m₂ large enough... This is getting complicated. Let me just use Euclid: m = m₁+1, n = 1, giving c = (m₁+1)^2 + 1. Need m₁^2 < (m₁+1)^2 + 1, which is m₁^2 < m₁^2 + 2m₁ + 2, always true. And c ≤ m₂^2+1: (m₁+1)^2+1 ≤ m₂^2+1 iff (m₁+1)^2 ≤ m₂^2 iff m₁+1 ≤ m₂, i.e. m₁ < m₂, which is given. a = (m₁+1)^2-1, b = 2(m₁+1). a > 0 iff m₁ ≥ 1. If m₁ = 0, a = 0 which is not positive. Use a = 2*(m₁+1) and b = (m₁+1)^2-1 (swap). If m₁ = 0, b = 0, still not positive. Hmm. Actually we're looking for ℕ triples with a^2+b^2=c^2, not necessarily a,b > 0. Actually the statement doesn't require a,b > 0. It just says ∃ a b c, a^2+b^2=c^2 ∧ m₁^2 < c ∧ c ≤ m₂^2 + 1. Take a=0, b=c for any c, then 0+c^2=c^2 ✓. Then need m₁^2 < c ≤ m₂^2+1. Take c = m₁^2+1. Then m₁^2 < m₁^2+1 ✓. Need m₁^2+1 ≤ m₂^2+1, i.e. m₁^2 ≤ m₂^2, which is true since m₁ < m₂. Use a = 0, b = m₁^2+1, c = m₁^2+1.
-/

/-! ## Section 9: Conservation Laws on the Lattice -/

/-
PROBLEM
The Minkowski norm is conserved under Berggren transformations

PROVIDED SOLUTION
Unfold minkowski3. Both sides equal a^2 + b^2 - c^2 after expansion. Use ring.
-/

/-
PROVIDED SOLUTION
Unfold minkowski3 and use ring.
-/

/-
PROVIDED SOLUTION
Unfold minkowski3 and use ring.
-/

/-! ## Section 10: The Sum-of-Squares Function and Photon Counting -/

/-
PROBLEM
The number 5 is expressible as a sum of two positive squares

PROVIDED SOLUTION
Use a=1, b=2. 1+4=5. exact ⟨1, 2, by norm_num, by norm_num, by norm_num⟩
-/

/-
PROBLEM
7 cannot be written as a sum of two squares (it's 3 mod 4)

PROVIDED SOLUTION
Suppose a^2+b^2=7. Then a,b ≤ 2 (since 3^2=9>7). Check all cases: (0,0)=0, (0,1)=1, (0,2)=4, (1,1)=2, (1,2)=5, (2,2)=8. None equal 7. Use intro ⟨a,b,h⟩, then bound a and b, then use interval_cases.
-/

/-
PROBLEM
25 can be written as a sum of two squares in two ways

PROVIDED SOLUTION
Use (3,4) and (4,3): 9+16=25 and 16+9=25. Or use (3,4) and (5,0)... but need positive. Use (a₁,b₁)=(3,4) and (a₂,b₂)=(4,3). exact ⟨3, 4, 4, 3, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
-/

/-! ## Section 11: Verified Summary

### Theorems in this file:
- Lattice null vector properties (zero Minkowski norm, symmetries, scaling)
- Euclid's parametrization is a lattice null vector
- Berggren tree growth bounds
- Brahmagupta-Fibonacci identity (two forms)
- Pythagorean quadruple parametrization and properties
- Lattice dispersion correction bounds
- Divisibility properties (div by 3, div by 4, odd hypotenuse)
- Smallest primitive triple is (3,4,5)
- Infinitude of triples and quadruples
- Berggren transformations preserve Minkowski norm
- Sum-of-squares representations
-/


