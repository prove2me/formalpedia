-- Prove2me | Theorems.Thm_Heisenberg125_Heis_length_le_of_const_image
-- name    : Heisenberg125.Heis.length_le_of_const_image
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T18:49:27.41771+00:00
-- url     : https://prove2.me/theorems/ee76c286-7e06-4bfa-a02b-37de7bb2735d
-- title:
--   Spread bound in a coset of the centre.
-- statement:
--   **Spread bound in a coset of the centre.**  In a product-one-free sequence
--   over the odd-exponent Heisenberg group, at most `2p - 2` entries can lie in one
--   coset of the centre.
--
--   ```lean
--   theorem Heisenberg125.Heis.length_le_of_const_image(hodd : Odd p) {C : List (Heis p)} {α β : ZMod p}
--       (hfree : ProductOneFree C) (hconst : ∀ g ∈ C, g.a = α ∧ g.b = β) :
--       C.length ≤ 2 * p - 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/Heisenberg125/CosetBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/Heisenberg125/CosetBound.lean#L61

-- Thm stub generated from Algebra/Heisenberg125/CosetBound.lean
import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
import Definitions.Def_Algebra_Heisenberg125_CosetBound
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

open Heisenberg125

open Heis

variable {p : ℕ}

theorem Heisenberg125.Heis.length_le_of_const_image(hodd : Odd p) {C : List (Heis p)} {α β : ZMod p}
    (hfree : ProductOneFree C) (hconst : ∀ g ∈ C, g.a = α ∧ g.b = β) :
    C.length ≤ 2 * p - 2 := by sorry
