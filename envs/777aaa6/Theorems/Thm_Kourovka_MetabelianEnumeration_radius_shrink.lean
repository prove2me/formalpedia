-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_radius_shrink
-- name    : Kourovka.MetabelianEnumeration.radius_shrink
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:40:31.857639+00:00
-- url     : https://prove2.me/theorems/331548df-d667-47ed-9bcc-e1085384daef
-- title:
--   Metabelian Enumeration: radius shrink
-- statement:
--   The strict scalar estimate in (17.124.5), including the radius margin.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/Radius.lean#L18-L29
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/Radius.lean#L18-L29

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic
import Definitions.Def_Kourovka_Polyhedral_Radius
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration

theorem Kourovka.MetabelianEnumeration.radius_shrink (C D ρ δ r s : ℝ)
    (_hC : 0 < C) (hρC : C < ρ) (hρD : D ^ 2 < C * ρ)
    (hδ : 0 < δ) (hδC : δ ≤ C / 4)
    (hr : ρ ≤ r) (hr' : r < ρ + δ)
    (hs : s ≤ r ^ 2 - 2 * C * r + D ^ 2) : s < ρ ^ 2 := by sorry
