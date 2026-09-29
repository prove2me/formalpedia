-- Prove2me | Definitions.Def_Cryptography_IsogenySIDH_ModularTwoIsogeny
-- name    : Cryptography_IsogenySIDH_ModularTwoIsogeny
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:16:25.275521+00:00
-- url     : https://prove2.me/theorems/b21796fd-0468-4d7b-b3ea-894b22a3b681
-- title:
--   Aether Catalog definitions — Cryptography_IsogenySIDH_ModularTwoIsogeny
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.IsogenySIDH.ModularTwoIsogeny`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/IsogenySIDH/ModularTwoIsogeny.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_RadicalMontgomeryFormula
/-
# The radical Montgomery step is a genuine edge of the 2-isogeny graph

`RadicalMontgomeryFormula` produced an explicit rational map from `E_A` to a
generalized Montgomery curve with parameter `radTwoParam A α = (A+6)/(2α)`,
`α² = A + 2`.  That is a *local* verification: the formulas transport points.
This file supplies the *global* certificate that the construction really is a
2-isogeny, by checking it against the classical modular polynomial `Φ₂`.

The main results are:

* `jMont_radTwoParam` — the `j`-invariant of the target is
  `jQuot A = 16 (A²+12)³ / (A²-4)²`.  Remarkably the radical `α` cancels: the
  target `j` is a *rational* function of `A`.
* `jMont_model_independent` — the three Montgomery renormalisations of the
  quotient curve (obtained by moving each of its three two-torsion points to
  the origin, using the three radicals `√(A+2)`, `√(2-A)`, `√(A²-4)`) all have
  the same `j`-invariant `jQuot A`.  So the radical step is independent of the
  chosen model and of the sign of the radical.
* `modPoly2_jMont_jQuot` and `modPoly2_radical_step` — the pair
  `(j(E_A), j(E_{A'}))` is a zero of the level-2 modular polynomial `Φ₂`.  This
  is the definitive certificate of 2-isogeny, proved as a polynomial identity
  of degree 54 in `A`.
* `radChain_isTwoIsogenyPath` — an admissible radical walk traces a path in the
  2-isogeny graph, by induction along the walk.
* `two_isogeny_neighbours_card_le_three` — `Φ₂` is monic of degree three in each
  variable, so every vertex of the 2-isogeny graph has at most three neighbours;
  this bounds the branching of a radical walk and is what makes the walk a walk
  on a cubic (Ramanujan) graph.
-/

namespace Cryptography.IsogenySIDH

open Polynomial

variable {K : Type*} [Field K]

/-! ## `j`-invariants -/

/-- The `j`-invariant of the Montgomery curve `y² = x³ + A x² + x`. -/
def jMont (A : K) : K := 256 * (A ^ 2 - 3) ^ 3 / (A ^ 2 - 4)

/-- The `j`-invariant of the quotient of `E_A` by `⟨(0,0)⟩`, as a rational
function of `A` alone. -/
def jQuot (A : K) : K := 16 * (A ^ 2 + 12) ^ 3 / (A ^ 2 - 4) ^ 2



/-! ## The three Montgomery models of the quotient -/

/-- Renormalisation at the two-torsion point `X = -2` of the quotient curve,
using the radical `γ` with `γ² = 2 - A`. -/
def radTwoParamMinus (A γ : K) : K := (A - 6) / (2 * γ)

/-- Renormalisation at the two-torsion point `X = -A` of the quotient curve,
using the radical `δ` with `δ² = A² - 4`. -/
def radTwoParamCentre (A δ : K) : K := -(2 * A) / δ






/-! ## The level-2 modular polynomial -/

/-- The classical modular polynomial of level two,
`Φ₂(X,Y) = X³ + Y³ - X²Y² + 1488(X²Y + XY²) - 162000(X²+Y²) + 40773375XY
          + 8748000000(X+Y) - 157464000000000`. -/
def modPoly2 (X Y : K) : K :=
  X ^ 3 + Y ^ 3 - X ^ 2 * Y ^ 2 + 1488 * (X ^ 2 * Y + X * Y ^ 2)
    - 162000 * (X ^ 2 + Y ^ 2) + 40773375 * (X * Y)
    + 8748000000 * (X + Y) - 157464000000000





/-! ## Radical walks are paths in the 2-isogeny graph -/

/-- A sequence of `j`-invariants is a path in the 2-isogeny graph when every
consecutive pair is a zero of `Φ₂`. -/
def IsTwoIsogenyPath (j : ℕ → K) : Prop := ∀ n, modPoly2 (j n) (j (n + 1)) = 0

/-- A radical walk is *nonsingular* when every parameter it visits has
nonvanishing `A² - 4`, i.e. stays away from the two degenerate Montgomery
parameters `±2`. -/
def NonsingularWalk (r : ℕ → K) (A : K) : Prop :=
  AdmissibleWalk r A ∧ ∀ n, (radChain r A n) ^ 2 - 4 ≠ 0




/-! ## Degree bound: the 2-isogeny graph is cubic -/

/-- `Φ₂(j, ·)` as an honest univariate polynomial. -/
noncomputable def modPoly2Y (j : K) : K[X] :=
  C 1 * X ^ 3 + C (-(j ^ 2) + 1488 * j - 162000) * X ^ 2
    + C (1488 * j ^ 2 + 40773375 * j + 8748000000) * X
    + C (j ^ 3 - 162000 * j ^ 2 + 8748000000 * j - 157464000000000)





/-! ## How many Montgomery models does one `j`-invariant have? -/

/-- The polynomial whose roots are the Montgomery parameters with a prescribed
`j`-invariant: `256(A²-3)³ - j(A²-4)`. -/
noncomputable def montModelPoly (j : K) : K[X] :=
  C 256 * X ^ 6 - C 2304 * X ^ 4 + C (6912 - j) * X ^ 2 + C (4 * j - 6912)






end Cryptography.IsogenySIDH


