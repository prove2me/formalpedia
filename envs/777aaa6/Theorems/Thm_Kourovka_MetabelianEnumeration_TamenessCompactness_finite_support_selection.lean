-- Prove2me | Theorems.Thm_Kourovka_MetabelianEnumeration_TamenessCompactness_finite_support_selection
-- name    : Kourovka.MetabelianEnumeration.TamenessCompactness.finite_support_selection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T07:48:54.223286+00:00
-- url     : https://prove2.me/theorems/1cbe9e56-51d2-4c16-91a7-31a522b42e10
-- title:
--   Tameness Compactness: finite support selection
-- statement:
--   Any family of finite supports covering the nonzero directions admits a
--   finite subfamily. The selected indices retain an arbitrary original property.
--
--   Source: https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/TamenessCompactness.lean#L24-L53
-- source:
--   https://github.com/Achxy/k-17-124/blob/16624b89b2bb8c8c61f023bd153c6c60707720f3/Kourovka/Modules/TamenessCompactness.lean#L24-L53

import Definitions.Def_Kourovka_Covers_FiniteCover
import Definitions.Def_Kourovka_Modules_TamenessCompactness
set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.TamenessCompactness
open ConeVerifier FiniteCover

theorem Kourovka.MetabelianEnumeration.TamenessCompactness.finite_support_selection {k : ℕ} {ι : Type*}
    (support : ι → List (Vec k)) (admissible : ι → Prop)
    (h : ∀ x : Fin k → ℝ, x ≠ 0 →
      ∃ i, admissible i ∧ ∀ u ∈ support i, 0 < dot u x) :
    ∃ selected : List ι, (∀ i ∈ selected, admissible i) ∧
      ConeCover (selected.map support) := by sorry
