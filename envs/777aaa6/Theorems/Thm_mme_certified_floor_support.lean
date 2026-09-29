-- Prove2me | Theorems.Thm_mme_certified_floor_support
-- name    : mme_certified_floor_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-23T05:22:29.580018+00:00
-- url     : https://prove2.me/theorems/8c1895b7-e9dc-49d6-8fa5-bb6fb3944558
-- title:
--   A certified entropy floor only sees the support of its distribution
-- statement:
--   A certified entropy floor only sees the support of its distribution.
--
--   Both parts of the floor -- the quadratic part and each of the four logarithm coefficients -- are
--   sums of terms that vanish wherever the weight does. So the floor may be computed over any finite set
--   containing the support, and letters of weight zero cost nothing at all, whatever reference is
--   attached to them.
--
--   This matters in practice: a distribution can live in a large alphabet while being supported on a
--   handful of letters, and without this the certificate would pay for every letter.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_certified_generic_floor_data
import Definitions.Def_mme_certified_entropy_rational_data

open BigOperators MME MME.RegionRate MME.Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u

theorem mme_certified_floor_support :
    ∀ {W : Type u} [Fintype W] (p : W → ℚ) (e : W → Fin 4 → ℤ) (S : Finset W),
      (∀ w, w ∉ S → p w = 0) →
      regFloorG p e =
        (∑ w ∈ S, (p w - (p w) ^ 2 / qvalQ (e w))) -
          ∑ j, (if 0 ≤ (∑ w ∈ S, p w * ((e w j : ℤ) : ℚ)) then
                  (∑ w ∈ S, p w * ((e w j : ℤ) : ℚ)) * logHi j
                else (∑ w ∈ S, p w * ((e w j : ℤ) : ℚ)) * logLo j) := by sorry
