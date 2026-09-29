-- Prove2me | Definitions.Def_Algebra_Heisenberg125_CosetBound
-- name    : Algebra_Heisenberg125_CosetBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:33:54.109063+00:00
-- url     : https://prove2.me/theorems/e956afc8-8904-45c1-82a6-4c371daaa75f
-- title:
--   Aether Catalog definitions — Algebra_Heisenberg125_CosetBound
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.Heisenberg125.CosetBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/Heisenberg125/CosetBound.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
import Definitions.Def_Algebra_Heisenberg125_LowerBound
/-
# A spread bound: at most `2p - 2` entries in any coset of the centre

The centre of `H_{p^3}` is `⟨v⟩`, and the cosets of the centre are the fibres of
the projection `(a,b,c) ↦ (a,b)` onto `(ZMod p)^2`.

**Theorem** (`Heis.length_le_of_const_image`).  If `p` is odd and `C` is a
product-one-free sequence over `H_{p^3}` all of whose entries have the same
image `(α, β)` in `(ZMod p)^2`, then `|C| ≤ 2p - 2`.

The proof is a genuine cross-domain application of the **Erdős–Ginzburg–Ziv
theorem**: `2p - 1` entries in one coset contain `p` of them whose central
coordinates sum to zero; those `p` entries multiply (in any order) to
`(pα, pβ, Σc + (p choose 2) αβ) = 1`, using that `p` is odd so that
`p ∣ binom p 2`.

The bound is sharp: `v^{p-1}` and `x^{p-1}(xv)^{p-1}`-type sequences show that
`2p - 2` entries with equal image can occur inside a product-one-free sequence.
-/

namespace Heisenberg125

namespace Heis

variable {p : ℕ}





/-! ### Sharpness of the coset bound -/


/-- The sequence `x^{p-1} (xv)^{p-1}`, of length `2p - 2`, all of whose entries
lie in the single coset `(1, 0)` of the centre. -/
def cosetExtremalSeq (p : ℕ) : List (Heis p) :=
  List.replicate (p - 1) (⟨1, 0, 0⟩ : Heis p) ++ List.replicate (p - 1) (⟨1, 0, 1⟩ : Heis p)




end Heis

end Heisenberg125


