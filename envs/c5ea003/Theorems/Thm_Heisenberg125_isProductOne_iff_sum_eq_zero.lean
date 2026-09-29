-- Prove2me | Theorems.Thm_Heisenberg125_isProductOne_iff_sum_eq_zero
-- name    : Heisenberg125.isProductOne_iff_sum_eq_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T19:17:45.164989+00:00
-- url     : https://prove2.me/theorems/b465212e-088c-455e-833f-734c667a42e7
-- title:
--   Having product one in `Multiplicative A` means summing to zero in `A`.
-- statement:
--   Having product one in `Multiplicative A` means summing to zero in `A`.
--
--   ```lean
--   theorem Heisenberg125.isProductOne_iff_sum_eq_zero(L : List (Multiplicative A)) :
--       IsProductOne L ↔ (L.map toAdd).sum = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/Heisenberg125/AbelianDavenport.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/Heisenberg125/AbelianDavenport.lean#L36

-- Thm stub generated from Algebra/Heisenberg125/AbelianDavenport.lean
import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
import Definitions.Def_Algebra_Heisenberg125_LowerBound
import Definitions.Def_Algebra_Heisenberg125_ZeroSumTwoDim
/-
# Exact small Davenport constants of the abelian sections of `H_{p^3}`

`H_{p^3}` sits in the extension `C_p → H_{p^3} → C_p ⊕ C_p`, and the two
abelian groups involved are exactly the ones controlling our bounds.  Here we
compute their small Davenport constants exactly:

* `smallDavenport_multiplicative_zmod : d(C_p) = p - 1`,
* `smallDavenport_multiplicative_zmod_sq : d(C_p ⊕ C_p) = 2p - 2`.

The upper bound for `C_p` is the general pigeonhole bound `d(G) ≤ |G| - 1`; the
upper bound for `C_p ⊕ C_p` is the Chevalley–Warning bound of
`Algebra.Heisenberg125.ZeroSumTwoDim`.  Both lower bounds are explicit
zero-sum-free sequences.

Consequently `d(H_{p^3}) ≥ 3p - 3 = d(C_p) + d(C_p ⊕ C_p)`, i.e. the
conjectural value `3p - 3` is exactly the sum of the Davenport constants of the
abelian sub- and quotient group — this is the structural reason behind the
conjecture of Godara and Sarkar.
-/

open Heisenberg125

open Multiplicative

variable {A : Type*} [AddCommGroup A]

theorem Heisenberg125.isProductOne_iff_sum_eq_zero(L : List (Multiplicative A)) :
    IsProductOne L ↔ (L.map toAdd).sum = 0 := by sorry
