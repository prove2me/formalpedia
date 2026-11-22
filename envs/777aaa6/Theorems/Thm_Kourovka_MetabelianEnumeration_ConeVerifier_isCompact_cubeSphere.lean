-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_ConeVerifier_isCompact_cubeSphere
-- name    : Kourovka.MetabelianEnumeration.ConeVerifier.isCompact_cubeSphere
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:48:14.429449+00:00
-- url     : https://prove2.me/theorems/90b5a879-1aa0-40c0-97a9-e8eab58212cb
-- title:
--   Cone Verifier: is Compact cube Sphere
-- statement:
--   The Cone Verifier construction uses the is Compact cube Sphere property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeMargin.lean#L58-L72
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeMargin.lean#L58-L72

import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Definitions.Def_Kourovka_Polyhedral_ConeMargin
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.ConeVerifier

theorem Kourovka.MetabelianEnumeration.ConeVerifier.isCompact_cubeSphere (n : ℕ) : IsCompact {x : Fin n → ℝ | CubeSphere x} := by sorry
