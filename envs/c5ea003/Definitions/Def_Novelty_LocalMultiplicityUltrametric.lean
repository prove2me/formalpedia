-- Prove2me | Definitions.Def_Novelty_LocalMultiplicityUltrametric
-- name    : Novelty_LocalMultiplicityUltrametric
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:32:20.985137+00:00
-- url     : https://prove2.me/theorems/deff43b5-5f0f-4a90-b3da-676fb23da44d
-- title:
--   Aether Catalog definitions — Novelty_LocalMultiplicityUltrametric
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.LocalMultiplicityUltrametric`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/LocalMultiplicityUltrametric.lean by skeleton subtraction
import Mathlib
/-
# The Local Obstruction to Naive Higher-Genus Factorization (contrarian)

The genus-0 Giampietro–Darmon formula expresses the `p`-adic valuation of a
cross-ratio as an alternating sum of local intersection multiplicities
`m(x,y) = v_p(x - y)`. A tempting **bold conjecture** for the higher-genus
setting is that these local intersection multiplicities compose *additively*
along a chain of CM points:
`m(x, z) = m(x, y) + m(y, z)`.
This would make the local factorization purely combinatorial and would predict
that no global correction is ever needed.

We **disprove** this conjecture: local intersection multiplicities are *not*
additive (`chain_additivity_fails`). What is true instead is the **ultrametric
(strong triangle) inequality** (`localMult_ultrametric`), and — sharpening it —
an exact equality when the two multiplicities differ (`localMult_isosceles`).
This ultrametric behaviour is exactly the local reason a nontrivial global
obstruction (the Néron–Tate height pairing) is forced upon the higher-genus
factorization.

## Main results
* `localMult_symm` — symmetry of the local intersection multiplicity.
* `localMult_ultrametric` — the strong triangle inequality.
* `localMult_isosceles` — sharp equality when the two multiplicities differ.
* `chain_additivity_fails` — an explicit counterexample disproving additivity.
-/

open scoped BigOperators

namespace GiampietroDarmon

/-- The **local intersection multiplicity** at `p` of two CM points `x, y`,
modelled as the `p`-adic valuation of their difference. -/
def localMult (p : ℕ) (x y : ℚ) : ℤ := padicValRat p (x - y)

/-
The local intersection multiplicity is symmetric.
-/

/-
**Ultrametric (strong triangle) inequality** for local intersection
multiplicities: the multiplicity of the "outer" pair is at least the minimum of
the two "inner" multiplicities.
-/

/-
**Sharp isosceles equality.** When the two inner multiplicities differ, the
ultrametric inequality is an equality: the outer multiplicity is exactly their
minimum.
-/

/-
**Disproof of naive chain-additivity.** With `p = 2` and the collinear
points `0, 1, 2` we have `m(0,1) = m(1,2) = 0` but `m(0,2) = 1`, so
`m(0,2) ≠ m(0,1) + m(1,2)`. Hence local intersection multiplicities are *not*
additive along chains, and the higher-genus factorization cannot be obtained by
naive local composition.
-/

end GiampietroDarmon


