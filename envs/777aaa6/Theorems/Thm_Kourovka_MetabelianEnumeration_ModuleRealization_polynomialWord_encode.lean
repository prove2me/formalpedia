-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ModuleRealization_polynomialWord_encode
-- name    : Kourovka.MetabelianEnumeration.ModuleRealization.polynomialWord_encode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:58:14.917717+00:00
-- url     : https://prove2.me/theorems/38250598-922e-4592-9550-745eb2d3e40b
-- title:
--   Module Realization: polynomial Word encode
-- statement:
--   A positive or negative tagged polynomial evaluates to its original module
--   action. For negative tags, exponent negation and the literal inverse cancel.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/ModuleRealization.lean#L82-L96
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/ModuleRealization.lean#L82-L96

import Definitions.Def_Kourovka_Modules_SignedTameness
import Definitions.Def_Kourovka_Modules_ModuleRealization
set_option autoImplicit true
noncomputable section
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ModuleRealization
open FiniteCover ValuationModule SignedTameness TamenessCompactness
variable {k : ℕ} {M G : Type*} [AddCommGroup M] [Group G]
  [Module (GroupRing (Lattice k)) M]

theorem Kourovka.MetabelianEnumeration.ModuleRealization.polynomialWord_encode (j : Multiplicative M →* G) (t : Fin k → G)
    (h : ActionCompatible j t) (p : SignedPolynomial k) (m : M) :
    polynomialWord t (j (Multiplicative.ofAdd m)) (encodeSigned p) =
      j (Multiplicative.ofAdd (p.2 • m)) := by sorry
