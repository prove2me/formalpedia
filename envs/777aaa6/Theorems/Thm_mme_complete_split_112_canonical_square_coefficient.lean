-- Prove2me | Theorems.Thm_mme_complete_split_112_canonical_square_coefficient
-- name    : mme_complete_split_112_canonical_square_coefficient
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T10:45:16.395598+00:00
-- url     : https://prove2.me/theorems/db852a67-d295-4e83-aa0c-a58a975dd2c7
-- title:
--   Canonical 112 projection preserves selected square coefficients
-- statement:
--   For any field $K$ and nonnegative integer $q$, consider the canonical $(1,1,2)$ constituent of the Kronecker square of the Coppersmith–Winograd tensor $\mathrm{CW}_q$. In each mode choose a canonical coordinate pair whose total grade is the specified component of $(1,1,2)$. The coefficient of the constituent in its inherited subset basis equals the coefficient of the full square at those same pairs:
--   $$[p_0,p_1,p_2]T_{112}=[\bar p_0,\bar p_1,\bar p_2](\mathrm{CW}_q\otimes\mathrm{CW}_q).$$
--   Here $\bar p_i$ forgets the proof that the coordinate pair belongs to its coarse class. The statement identifies literal basis coefficients, and does not assert any asymptotic value or multiplicity bound.
-- source:
--   Canonical-to-intact tensor transport: finite coordinate maps and coefficient preservation.

import Definitions.Def_mme_complete_split_112_canonical_source_data
import Definitions.Def_mme_TypeGrading_kron
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

open MME MME.CompleteSplit112 MME.DWZComponentRestriction Module PiTensorProduct
universe u
set_option autoImplicit false

theorem mme_complete_split_112_canonical_square_coefficient (K : Type u) [Field K] (q : ℕ)
    (p : ∀ i, CanonicalCoord.{u} q i) :
    (Basis.piTensorProduct (canonicalBasis K q)).repr (canonicalObj K q).t p =
      (Basis.piTensorProduct (cwSquareCanonicalBasis K q)).repr
        ((CWObj K q).kron (CWObj K q)).t (fun i ↦ (p i).down.val) := by sorry
