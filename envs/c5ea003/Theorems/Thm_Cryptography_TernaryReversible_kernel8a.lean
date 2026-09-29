-- Prove2me | Theorems.Thm_Cryptography_TernaryReversible_kernel8a
-- name    : Cryptography.TernaryReversible.kernel8a
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:45:03.951478+00:00
-- url     : https://prove2.me/theorems/250515df-423b-4544-80a0-350b24b59808
-- title:
--   Kernel8a
-- statement:
--   Formal statement of `Cryptography.TernaryReversible.kernel8a` from the Aether Catalog (Cryptography). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Cryptography.TernaryReversible.kernel8a{α β γ δ : Alph}
--       (h : ∀ i : ZMod 8, α * kv8a (i - 1) + β * kv8a i + γ * kv8a (i + 1) = 0) :
--       ¬ CycleBijective (addRule α β γ δ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/TernaryReversible/Additive.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/TernaryReversible/Additive.lean#L127

-- Thm stub generated from Cryptography/TernaryReversible/Additive.lean
import Mathlib
import Definitions.Def_Cryptography_TernaryReversible_Additive
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

open Cryptography
open TernaryReversible




/-! ## The kernel obstruction -/



/-! ### The five kernel configurations

`𝔽₃` has roots of unity of orders `1, 2, 4, 8` in its algebraic closure (`𝔽₉ˣ` is cyclic
of order `8`), which is why cycles of these four lengths suffice. -/

theorem Cryptography.TernaryReversible.kernel8a{α β γ δ : Alph}
    (h : ∀ i : ZMod 8, α * kv8a (i - 1) + β * kv8a i + γ * kv8a (i + 1) = 0) :
    ¬ CycleBijective (addRule α β γ δ) := by sorry
