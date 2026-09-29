-- Prove2me | Definitions.Def_Cryptography_IsogenySIDH_SupersingularRadicalExistence
-- name    : Cryptography_IsogenySIDH_SupersingularRadicalExistence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:17:56.451105+00:00
-- url     : https://prove2.me/theorems/7a720709-6595-4e48-abf4-f16603d1752d
-- title:
--   Aether Catalog definitions — Cryptography_IsogenySIDH_SupersingularRadicalExistence
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.IsogenySIDH.SupersingularRadicalExistence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/IsogenySIDH/SupersingularRadicalExistence.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_ModularTwoIsogeny
/-
# Radicals always exist over quadratic finite fields

Radical isogeny algorithms are run on supersingular curves over `𝔽_{p²}`.  A
radical 2-isogeny step from the Montgomery parameter `A` needs a square root of
`A + 2`; if that root is missing one has to change the Montgomery model, using
instead `√(2-A)` or `√(A²-4)` (see `ModularTwoIsogeny`, where all three models
were shown to hit the same point of the `j`-line).

The main theorem of this file, `exists_radical_of_isSquare_neg_one`, is that at
least one of these three radicals is *always* available, as soon as `-1` is a
square in the base field.  The proof is a quadratic-character computation
resting on the identity

`(A+2)·(2-A) = -(A²-4)`,

so the three radicands multiply to minus a square: their quadratic characters
cannot all be `-1`.

`isSquare_neg_one_of_card_sq` specialises this to a field of square
cardinality — exactly the quadratic finite fields `𝔽_{p²}` of supersingular
isogeny cryptography — where `-1` is automatically a square.  Combined with the
model-independence theorem of `ModularTwoIsogeny` this yields
`exists_montgomery_quotient_model`: over `𝔽_{p²}` the 2-isogenous curve always
has a Montgomery model defined over the same field, so a radical walk never
needs a field extension.

The final section records small, fully checked supersingular instances of the
radical step, verified by `decide`.
-/

namespace Cryptography.IsogenySIDH

open Finset

/-! ## Existence of one of the three radicals -/

section RadicalExistence

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]






end RadicalExistence

/-! ## Verified supersingular instances

For a prime `p ≡ 3 mod 4` the curve `y² = x³ + x` over `𝔽_p` is supersingular,
so it has exactly `p + 1` points.  We check this and the corresponding radical
step by exhaustive computation. -/

section Instances

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 23) := ⟨by norm_num⟩

/-- The affine points of the generalized Montgomery curve `B y² = x³ + A x² + x`
over `ZMod p`. -/
def affineMontPoints (p : ℕ) [NeZero p] (B A : ZMod p) : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter fun P => B * P.2 ^ 2 = P.1 ^ 3 + A * P.1 ^ 2 + P.1

/-- Number of projective points: the affine ones plus the single point at
infinity of a Montgomery model. -/
def montPointCount (p : ℕ) [NeZero p] (B A : ZMod p) : ℕ :=
  (affineMontPoints p B A).card + 1











end Instances

end Cryptography.IsogenySIDH


