-- Prove2me | Theorems.Thm_mult_eq_one_of_disjoint
-- name    : mult_eq_one_of_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:54:49.216355+00:00
-- url     : https://prove2.me/theorems/7b2d8638-cd0e-4420-99fe-06f57e955a6c
-- title:
--   mult eq one of disjoint: mult eq one of disjoint
-- statement:
--   Three pairwise disjoint `k`-subsets of `Fin (3k)` cover every point exactly once.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/Solution.lean#L22-L35
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/Solution.lean#L22-L35

module
public import Mathlib
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_Counting
public import Definitions.Def_SCCThm8_Numeric
public import Definitions.Def_SCCThm8_Degeneration
public import Definitions.Def_SCCThm8_PowerDegeneration
public import Definitions.Def_SCCGroupBarrier_Solution
set_option autoImplicit true
@[expose] public section
public section
open Finset

theorem mult_eq_one_of_disjoint (k : ℕ) (A B C : Finset (Fin (3 * k)))
    (hA : A.card = k) (hB : B.card = k) (hC : C.card = k)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C) (i : Fin (3 * k)) :
    SCCThm8.mult A B C i = 1 := by sorry
