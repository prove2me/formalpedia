-- Prove2me | Definitions.Def_EML_EMLDiffObstruction
-- name    : EML_EMLDiffObstruction
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:21:12.375396+00:00
-- url     : https://prove2.me/theorems/01d3b998-7509-49d9-a506-f2a8088e9b9c
-- title:
--   Aether Catalog definitions — EML_EMLDiffObstruction
-- statement:
--   Definition bundle for the Aether Catalog module `EML.EMLDiffObstruction`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from EML/EMLDiffObstruction.lean by skeleton subtraction
import Mathlib

/-!
# Polynomial Obstruction Theory for ODE Solvability

This file establishes formal obstruction theory for polynomial solvability of
linear ordinary differential equations, centered on Airy's equation y″ = xy
as the prototypical barrier.

## Main Results

* `no_poly_solves_airy` — No nonzero polynomial satisfies y″ = X·y
* `no_poly_solves_second_order_pos_deg` — General degree obstruction: for any
  polynomial coefficient q of positive degree, y″ = q·y has no nonzero polynomial solution
* `poly_wronskian_derivative_zero` — The polynomial Wronskian W(f,g) = f·g' - g·f'
  has zero derivative when f and g both satisfy y″ = q·y
* `no_poly_solves_riccati_airy` — No polynomial satisfies the associated Riccati
  equation v' + v² = X

## Mathematical Context

The impossibility of solving Airy's equation y″ = xy in terms of elementary
functions begins with the most basic obstruction: no polynomial can satisfy it.
The key insight is a degree mismatch: for y″ = q(x)·y with deg(q) ≥ 1,
the right side q·y has degree deg(q) + deg(y), strictly greater than deg(y),
while the left side y″ has degree strictly less than deg(y). This makes
equality impossible for any nonzero polynomial y.

The Wronskian result is the polynomial-ring analogue of Abel's identity from
ODE theory. The Riccati obstruction connects to differential Galois theory:
if Airy's equation had a Liouvillian solution, the associated Riccati equation
would have an algebraic (in particular, polynomial) solution.
-/

open Polynomial

namespace EMLDiffObstruction

/-! ### Degree comparison lemma -/

/-
!-- The core degree argument: for p ≠ 0, degree(p'') < degree(X · p).
This follows because degree(p'') < degree(p) ≤ degree(p) + 1 = degree(X · p),
using that derivative strictly decreases degree of nonzero polynomials. -- !--

The degree of the second derivative of a nonzero polynomial is strictly less
than the degree of X times that polynomial. This is the core degree mismatch
underlying all polynomial obstruction arguments for second-order ODEs.
-/

/-! ### Airy equation obstruction -/

/-
!-- No nonzero polynomial satisfies y'' = xy. Proof: by the degree comparison
lemma, degree(p'') < degree(X·p), so they cannot be equal. -- !--

**Airy polynomial obstruction**: No nonzero polynomial satisfies the Airy
equation y″ = xy in the polynomial ring ℝ[X].
-/

/-! ### General degree obstruction -/

/-
!-- For any polynomial q with natDegree ≥ 1 and nonzero p, we have
degree(p'') < degree(p) ≤ degree(q·p), so p'' ≠ q·p. -- !--

**General polynomial ODE obstruction**: For any polynomial coefficient q of
positive degree, the equation y″ = q·y has no nonzero polynomial solution.
This generalizes the Airy case (q = X) to arbitrary polynomial coefficients
like q = X², X³, X² + X, etc.
-/

/-! ### Polynomial Wronskian theory -/

/-- The polynomial Wronskian of two polynomials f and g, defined as
W(f,g) = f · g' - g · f'. This is the polynomial-ring analogue of the
classical Wronskian from ODE theory. -/
noncomputable def polyWronskian (f g : Polynomial ℝ) : Polynomial ℝ :=
  f * derivative g - g * derivative f

/-
!-- If f'' = q·f and g'' = q·g, then W'(f,g) = f·g'' - g·f'' = f·(q·g) - g·(q·f) = 0.
This is the polynomial-ring version of Abel's identity. -- !--

**Wronskian constancy (Abel's identity)**: If f and g both satisfy y″ = q·y
in the polynomial ring, then their Wronskian has zero derivative. This is the
polynomial analogue of the classical result that the Wronskian of solutions to
a second-order linear ODE without first-derivative term is constant.
-/

/-! ### Riccati equation obstruction -/

/-
!-- No polynomial solves v' + v² = X. If deg(p) = 0, then p is constant c,
so 0 + c² = X, but c² is constant. If deg(p) ≥ 1, then deg(p²) = 2·deg(p) ≥ 2
but deg(p') < deg(p) ≤ deg(p²), so deg(p' + p²) = deg(p²) = 2·deg(p),
which must equal deg(X) = 1, giving 2·deg(p) = 1, impossible in ℕ. -- !--

**Riccati polynomial obstruction**: No polynomial satisfies the Riccati equation
v' + v² = X associated with Airy's equation. The proof combines a degree parity
argument (deg(v²) = 2·deg(v) is even but deg(X) = 1 is odd) with a constant-case
analysis. This obstruction connects to differential Galois theory: if Airy's
equation had a Liouvillian solution, this Riccati equation would have a rational
(and in particular, potentially polynomial) solution.
-/

/-! ### Degree mismatch for higher-order terms -/

/-
!-- X^n · p has natDegree = n + natDegree(p), but p'' has natDegree ≤ natDegree(p) - 2.
For n ≥ 1, this gives n + natDegree(p) > natDegree(p) - 2. -- !--

No nonzero polynomial satisfies y″ = Xⁿ·y for any n ≥ 1.
This is a corollary of the general degree obstruction, but stated
in a form that directly applies to the family of generalized Airy equations.
-/

end EMLDiffObstruction


