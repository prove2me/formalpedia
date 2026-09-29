-- Prove2me | Definitions.Def_Evergreen_Pythagorean_UniversalParent
-- name    : Evergreen_Pythagorean_UniversalParent
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T16:38:13.237776+00:00
-- url     : https://prove2.me/theorems/d02cbec7-871f-4cfa-aa1b-50116758e12e
-- title:
--   Aether Catalog definitions — Evergreen_Pythagorean_UniversalParent
-- statement:
--   Definition bundle for the Aether Catalog module `Evergreen.Pythagorean.UniversalParent`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Evergreen/Pythagorean/UniversalParent.lean by skeleton subtraction
import Mathlib

/-!
# Universal Parent Equation for Pythagorean Triple Trees

## Overview

Every primitive Pythagorean triple (PPT) lies in a ternary tree rooted at (3,4,5).
Three well-known tree structures enumerate all PPTs:

1. **Berggren tree** (1934): matrices B₁, B₂, B₃ acting on (a,b,c)
2. **Price tree** (2008): matrices P₁, P₂, P₃ (alternative generators for the same group)
3. **Euclid-parameter tree**: matrices M₁, M₂, M₃ acting on (m,n) with a=m²-n², b=2mn, c=m²+n²

All three are free bases for the same free group of rank 3 inside O(2,1;ℤ),
the integer Lorentz group preserving the quadratic form a²+b²-c²=0.

### The Universal Parent Equation

Given any PPT (a₁,b₁,c₁) ≠ (3,4,5), the **parent** is the unique PPT (a₂,b₂,c₂)
from which (a₁,b₁,c₁) was generated. The parent hypotenuse is always:

  **c₂ = 3c₁ - 2a₁ - 2b₁**

The legs depend on which branch was taken:
- Branch 1: a₂ = a₁ + 2b₁ - 2c₁, b₂ = 2c₁ - 2a₁ - b₁
- Branch 2: a₂ = a₁ + 2b₁ - 2c₁, b₂ = 2a₁ + b₁ - 2c₁
- Branch 3: a₂ = 2c₁ - a₁ - 2b₁, b₂ = 2a₁ + b₁ - 2c₁

The branch is uniquely determined by sign analysis.

### Recursive Parent Function

f⁽¹⁾(a₁,b₁,c₁) = (a₂,b₂,c₂)                    [parent]
f⁽²⁾(a₁,b₁,c₁) = f⁽¹⁾(a₂,b₂,c₂) = (a₃,b₃,c₃)  [grandparent]
f⁽ⁿ⁾(a₁,b₁,c₁) = f⁽ⁿ⁻¹⁾(a₂,b₂,c₂)              [nth ancestor]

Eventually f⁽ᵈ⁾(a₁,b₁,c₁) = (3,4,5) for some depth d.

### Factoring Connection

For an odd composite N = p·q, the trivial triple (N, (N²-1)/2, (N²+1)/2) descends
through the tree. At each level, gcd(leg, N) may reveal a nontrivial factor.
The descent makes the entire equation integral because it terminates at (3,4,5).
-/

open Matrix Finset

/-! ## Part 1: The Three Tree Generators -/

section TreeGenerators

/-! ### Generator 1: Berggren Tree (3×3 matrices on triples) -/







/-! ### Generator 2: Price Tree (alternative 3×3 matrices)

The Price tree (2008) uses an alternative set of free generators for the
same free group in O(2,1;ℤ). These are products of pairs of Berggren matrices. -/




/-! ### Generator 3: Euclid Parameter Tree (2×2 matrices on (m,n))

Every PPT has the form (m²-n², 2mn, m²+n²) for unique m > n > 0 with
gcd(m,n)=1 and m-n odd. The 2×2 matrices act on the (m,n) parameter space. -/




end TreeGenerators

/-! ## Part 2: The Universal Parent Equation -/

section UniversalParent



/-- Apply Berggren inverse B₁⁻¹ as a function on triples. -/
def invB1 (a b c : ℤ) : ℤ × ℤ × ℤ :=
  (a + 2*b - 2*c, -2*a - b + 2*c, -2*a - 2*b + 3*c)

/-- Apply Berggren inverse B₂⁻¹ as a function on triples. -/
def invB2 (a b c : ℤ) : ℤ × ℤ × ℤ :=
  (a + 2*b - 2*c, 2*a + b - 2*c, -2*a - 2*b + 3*c)

/-- Apply Berggren inverse B₃⁻¹ as a function on triples. -/
def invB3 (a b c : ℤ) : ℤ × ℤ × ℤ :=
  (-a - 2*b + 2*c, 2*a + b - 2*c, -2*a - 2*b + 3*c)

/-- **The Universal Parent Equation**: Given a PPT (a,b,c), find the unique
    parent by selecting the inverse branch that produces all-positive components.

    The parent hypotenuse is ALWAYS c' = 3c - 2a - 2b (universal across all branches).
    The branch selection determines only the leg assignment.

    Branch classification (for a odd, b even):
    - Branch 1: 2c > 2a + b (b relatively large)
    - Branch 2: 2a + b > 2c and a + 2b > 2c (both large)
    - Branch 3: 2c > a + 2b (a relatively large)
-/
def universalParent (a b c : ℤ) : ℤ × ℤ × ℤ :=
  if -2*a - b + 2*c > 0 then
    -- Branch 1 (B₁⁻¹): parent = (a+2b-2c, -2a-b+2c, -2a-2b+3c)
    invB1 a b c
  else if -a - 2*b + 2*c > 0 then
    -- Branch 3 (B₃⁻¹): parent = (-a-2b+2c, 2a+b-2c, -2a-2b+3c)
    invB3 a b c
  else
    -- Branch 2 (B₂⁻¹): parent = (a+2b-2c, 2a+b-2c, -2a-2b+3c)
    invB2 a b c


/-! ### Recursive Parent: f⁽ⁿ⁾ -/

/-- **Recursive parent function**: apply universalParent n times.
    f⁽⁰⁾(a,b,c) = (a,b,c)
    f⁽¹⁾(a,b,c) = parent(a,b,c)
    f⁽ⁿ⁾(a,b,c) = f⁽¹⁾(f⁽ⁿ⁻¹⁾(a,b,c))

    This is the nested recursive parent the user requested:
    f(1)(a₁,b₁,c₁) = (a₂,b₂,c₂)
    f(2)(a₁,b₁,c₁) = f(1)(a₂,b₂,c₂) = (a₃,b₃,c₃)
    f(3)(a₁,b₁,c₁) = f(2)(a₂,b₂,c₂) = f(1)(a₃,b₃,c₃) = (a₄,b₄,c₄)
-/
def parentN : ℕ → ℤ × ℤ × ℤ → ℤ × ℤ × ℤ
  | 0, t => t
  | n + 1, (a, b, c) =>
    let p := universalParent a b c
    parentN n p



end UniversalParent

/-! ## Part 3: Key Theorems -/

section KeyTheorems












end KeyTheorems

/-! ## Part 4: The Factoring Connection -/

section Factoring






end Factoring

/-! ## Part 5: Computational Experiments -/

section Experiments

-- Verify the universal parent on known triples
-- Verify recursive parent (depth 2 triples)
-- Full ancestry chains
-- Depth computation
-- Factoring experiments
-- All factors found during descent
-- Larger composites
-- Verify the recursive parent identity:
-- f(2)(a,b,c) = f(1)(f(1)(a,b,c))
-- Branch encoding: which branches are taken during descent?

end Experiments

/-! ## Part 6: The Closed-Form Universal Parent (Single Equation)

We can express the universal parent as a SINGLE equation using absolute values
and sign functions, eliminating the branch selection:

More elegantly, we observe:
  - The parent hypotenuse is ALWAYS c' = 3c - 2a - 2b (no branching needed)
  - The parent legs are: {|a + 2b - 2c|, |2a + b - 2c|} (the two positive values)
  - One of these equals a' and the other b', with the odd one being a' and even being b'
-/

section ClosedForm





end ClosedForm

/-! ## Part 7: Connection Between All Three Trees

All three tree structures (Berggren, Price, Euclid-parameter) are related
by conjugation in the automorphism group. The universal parent equation
in each coordinate system:

### Berggren coordinates (a, b, c):
  c_parent = 3c - 2a - 2b

### Euclid coordinates (m, n) where a=m²-n², b=2mn, c=m²+n²:
  The parent (m', n') satisfies a relationship through the 2×2 inverse matrices.

### Price coordinates:
  Different branch selection rules, same terminal behavior.
-/

section TreeCorrespondence

/-- Convert Euclid parameters to a Pythagorean triple. -/
def euclidToTriple (m n : ℤ) : ℤ × ℤ × ℤ :=
  (m^2 - n^2, 2*m*n, m^2 + n^2)




end TreeCorrespondence

/-! ## Part 8: The Integrality Theorem -/

section Integrality





end Integrality

/-! ## Part 9: Parity Analysis for Factoring -/

section ParityAnalysis



/-
**Parity invariant**: a + b + c ≡ 0 (mod 2) for all PPTs with a odd, b even.
    Since a²+b²=c², a odd ⟹ a² odd, b even ⟹ b² even, so c² odd ⟹ c odd.
    Thus a+b+c = odd+even+odd = even.
-/

end ParityAnalysis


