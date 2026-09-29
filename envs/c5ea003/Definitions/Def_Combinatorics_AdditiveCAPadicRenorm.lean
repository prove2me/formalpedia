-- Prove2me | Definitions.Def_Combinatorics_AdditiveCAPadicRenorm
-- name    : Combinatorics_AdditiveCAPadicRenorm
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:28:25.947472+00:00
-- url     : https://prove2.me/theorems/2c384240-1996-4f24-a93f-457669e2303b
-- title:
--   Aether Catalog definitions — Combinatorics_AdditiveCAPadicRenorm
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.AdditiveCAPadicRenorm`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/AdditiveCAPadicRenorm.lean by skeleton subtraction
import Mathlib
/-
# Prime-power renormalization of the additive cellular automaton

NOTE (restored module).  `Novelty/PadicFractalUncertainty.lean` imports this module and uses
`AdditiveCA.caOp` and `AdditiveCA.caOp_renorm`, but the file itself was missing from the
catalogue, so nothing downstream compiled.  This file restores it with complete proofs.

The additive ("Rule 90") cellular automaton on bi-infinite configurations over `ZMod p` sends a
configuration to the sum of its two neighbours.  Encoding configurations as Laurent
polynomials, the automaton is multiplication by `caOp p = T 1 + T (-1)`.

The main result, `caOp_renorm`, is the *exact two-ray renormalization identity*: iterating the
automaton `p ^ k` times produces exactly two light rays, at offsets `± p ^ k`.  It is the
freshman's dream in characteristic `p`, applied in the Laurent polynomial ring.
-/

open LaurentPolynomial

namespace AdditiveCA

/-- The transition operator of the additive ("Rule 90") cellular automaton over `ZMod p`,
seen as the Laurent polynomial `T + T⁻¹`: a cell becomes the sum of its two neighbours. -/
noncomputable def caOp (p : ℕ) : LaurentPolynomial (ZMod p) := T 1 + T (-1)

/-- The Laurent polynomial ring over `ZMod p` has characteristic `p`. -/
instance charP_laurentPolynomial_zmod (p : ℕ) [Fact p.Prime] :
    CharP (LaurentPolynomial (ZMod p)) p := by
  refine charP_of_injective_ringHom
    (f := (Polynomial.toLaurent).comp (Polynomial.C (R := ZMod p))) ?_ p
  intro a b hab
  exact Polynomial.C_injective (Polynomial.toLaurent_injective hab)




end AdditiveCA


