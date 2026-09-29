-- Prove2me | Definitions.Def_Algebra_ProductQRDial
-- name    : Algebra_ProductQRDial
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:53:48.816711+00:00
-- url     : https://prove2.me/theorems/3d2fc856-03bf-4583-bab0-9278d762a69d
-- title:
--   Aether Catalog definitions — Algebra_ProductQRDial
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.ProductQRDial`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/ProductQRDial.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_ReciprocityFlipDial
/-
# The product QR dial: an XOR law, factor blindness, and where the flip lives

Formal core of experiment **577** (paper 227), arithmetic part.  The covariate
of the experiment is the *product dial*

  `W(N, P) = ∑_{ℓ ∈ P, N a QR mod ℓ} 1/ℓ`,

evaluated on semiprimes `N = p q`.  This file proves the three arithmetic facts
that govern its behaviour.

## Main results

* `ProductQRDial.qr_product_iff` — the **XOR law**: for a prime `ℓ` coprime to
  both factors, `p q` is a residue mod `ℓ` iff `p` and `p` have the *same*
  residue status.  The product dial reads a parity, not the factors.
* `ProductQRDial.qrWeight_blind` and `ProductQRDial.qrWeight_pp_eq_nn` — the
  resulting **factor blindness** of the weighted product dial: `PP` and `NN`
  factorisation types produce *identical* weighted dials, exactly as the
  extrinsic class-group representation vector of
  `Catalog/Algebra/ClassGroupResidueDial.lean` collapses `PP` and `NN`.
* `ProductQRDial.qrWeight_sq` — squares saturate the dial: every prime of the
  window contributes, so the dial is maximal on squares.
* `ProductQRDial.dial_forms_agree_on_one_mod_four` — **where the reciprocity
  artifact lives**: on a window consisting of primes `ℓ ≡ 1 (mod 4)` the
  composite-bottom (product) dial and the clean prime-bottom dial are *equal*.
  All of the discrepancy diagnosed in `Catalog/Algebra/ReciprocityFlipDial.lean`
  is carried by the `ℓ ≡ 3 (mod 4)` part of the window.
-/

namespace ProductQRDial

open Finset

/-! ## 1. The XOR law for the product dial -/



/-! ## 2. The weighted product dial -/

/-- The `1/ℓ`-weighted product dial of `N` over a window `P` of moduli. -/
noncomputable def qrWeight (N : ℤ) (P : Finset ℕ) : ℝ :=
  ∑ l ∈ P, if jacobiSym N l = 1 then (1 : ℝ) / l else 0





/-! ## 3. Where the reciprocity artifact lives -/



end ProductQRDial


