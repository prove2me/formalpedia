-- Prove2me | Definitions.Def_Kourovka_Polyhedral_ConeMargin
-- name    : Kourovka_Polyhedral_ConeMargin
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T07:42:15.044052+00:00
-- url     : https://prove2.me/theorems/f3d90e73-059f-47d3-86db-8cfd2b74501c
-- title:
--   Cone Margin
-- statement:
--   Definitions and structural lemmas for Cone Margin, from Achyuth Jayadevan's pinned Effective enumeration of metabelian presentations development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Polyhedral/ConeMargin.lean

import Definitions.Def_Kourovka_Polyhedral_ConeVerifier
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
set_option autoImplicit true
namespace Kourovka.MetabelianEnumeration.ConeVerifier
def supportScore {n : ℕ} : List (Vec n) → (Fin n → ℝ) → ℝ
  | [], _ => 1
  | u :: rest, x => min (dot u x) (supportScore rest x)
def coverScore {n : ℕ} : Supports n → (Fin n → ℝ) → ℝ
  | [], _ => 0
  | support :: rest, x => max (supportScore support x) (coverScore rest x)
end Kourovka.MetabelianEnumeration.ConeVerifier


