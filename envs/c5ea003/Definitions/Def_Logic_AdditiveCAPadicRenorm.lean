-- Prove2me | Definitions.Def_Logic_AdditiveCAPadicRenorm
-- name    : Logic_AdditiveCAPadicRenorm
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:24:40.449143+00:00
-- url     : https://prove2.me/theorems/10b10ec7-18ac-4d76-92b4-9ce7fc423b1f
-- title:
--   Aether Catalog definitions — Logic_AdditiveCAPadicRenorm
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.AdditiveCAPadicRenorm`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/AdditiveCAPadicRenorm.lean by skeleton subtraction
import Mathlib

/-!
# Frobenius renormalization of the additive cellular automaton

This module was referenced by `Novelty.PadicFractalUncertainty` but was not present in the
repository.  It is reconstructed here with the one definition and the one theorem that file
uses.

The additive ("rule 90") cellular automaton over `𝔽_p` is the Laurent polynomial operator
`caOp p = T + T⁻¹` acting on configurations `𝔽_p^ℤ`.  In characteristic `p` the freshman's
dream gives the exact renormalization `caOp p ^ (p ^ k) = T^(p^k) + T^(-p^k)`: after `p ^ k`
steps the automaton consists of exactly two light rays travelling at speed one, which is the
self-similarity responsible for the Pascal-triangle fractals.
-/

open LaurentPolynomial

namespace AdditiveCA

/-- The additive (rule 90) cellular automaton operator `T + T⁻¹` over `𝔽_p`. -/
noncomputable def caOp (p : ℕ) [Fact p.Prime] : LaurentPolynomial (ZMod p) := T 1 + T (-1)

instance charP_laurentPolynomial (p : ℕ) [Fact p.Prime] :
    CharP (LaurentPolynomial (ZMod p)) p :=
  charP_of_injective_ringHom (LaurentPolynomial.C (R := ZMod p)).injective p


end AdditiveCA


