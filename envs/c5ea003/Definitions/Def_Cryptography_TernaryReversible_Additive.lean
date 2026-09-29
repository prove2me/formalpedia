-- Prove2me | Definitions.Def_Cryptography_TernaryReversible_Additive
-- name    : Cryptography_TernaryReversible_Additive
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:23:52.743129+00:00
-- url     : https://prove2.me/theorems/23e7071e-4ba4-4e11-9995-49ce8690b599
-- title:
--   Aether Catalog definitions — Cryptography_TernaryReversible_Additive
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.TernaryReversible.Additive`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/TernaryReversible/Additive.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_TernaryReversible_Core

/-!
# The classification claim is *true* inside the affine class

The refutation files show that the single-coordinate classification claim fails for
general ternary radius-one rules.  This file proves the complementary positive result:
restricted to **affine rules over `𝔽₃`**

`addRule α β γ δ a b c = α * a + β * b + γ * c + δ`,

the claim is exactly right — such a rule is bijective on every nonempty finite cycle
**iff** exactly one of the three coefficients is nonzero, i.e. iff the rule is a single
coordinate followed by the permutation `x ↦ α x + δ`.

Conceptually the global map on the `n`-cycle is multiplication by the Laurent
polynomial `α x⁻¹ + β + γ x` in `𝔽₃[x]/(xⁿ - 1)`, so bijectivity for all `n` forces the
polynomial `α + β x + γ x²` to have no root among the roots of unity, i.e. no nonzero
root at all — which for a polynomial of degree `≤ 2` means it is a monomial.  The proof
below is the effective form of this statement: for each of the twenty-one bad
coefficient triples we exhibit an explicit nonzero kernel configuration on a cycle of
length `1`, `2`, `4` or `8` (these are exactly the orders of the roots of unity that can
occur over `𝔽₃`), and the six good triples are handled by the single-coordinate theorem.

## Main results

* `addRule_cycleBijective_iff` — the classification for affine rules;
* `not_cycleBijective_of_kernel` — the general kernel obstruction.
-/

namespace Cryptography
namespace TernaryReversible

/-- The affine radius-one rules over `𝔽₃`. -/
def addRule (α β γ δ : Alph) : LocalRule := fun a b c => α * a + β * b + γ * c + δ

/-- Exactly one of the three coefficients is nonzero. -/
def ExactlyOneNonzero (α β γ : Alph) : Prop :=
  (α ≠ 0 ∧ β = 0 ∧ γ = 0) ∨ (α = 0 ∧ β ≠ 0 ∧ γ = 0) ∨ (α = 0 ∧ β = 0 ∧ γ ≠ 0)

instance : ∀ α β γ, Decidable (ExactlyOneNonzero α β γ) := fun α β γ => by
  unfold ExactlyOneNonzero; infer_instance

/-! ## The kernel obstruction -/



/-! ### The five kernel configurations

`𝔽₃` has roots of unity of orders `1, 2, 4, 8` in its algebraic closure (`𝔽₉ˣ` is cyclic
of order `8`), which is why cycles of these four lengths suffice. -/

/-- The constant configuration on the `1`-cycle. -/
def kv1 : ZMod 1 → Alph := fun _ => 1

/-- The alternating configuration on the `2`-cycle. -/
def kv2 : ZMod 2 → Alph := ![2, 1]

/-- A kernel configuration on the `4`-cycle (order-`4` roots of unity). -/
def kv4 : ZMod 4 → Alph := ![2, 0, 1, 0]

/-- A kernel configuration on the `8`-cycle (order-`8` roots of unity). -/
def kv8a : ZMod 8 → Alph := ![1, 1, 2, 0, 2, 2, 1, 0]

/-- The second kernel configuration on the `8`-cycle. -/
def kv8b : ZMod 8 → Alph := ![1, 2, 2, 0, 2, 1, 1, 0]











/-! ## The two directions -/







end TernaryReversible
end Cryptography


