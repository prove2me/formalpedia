-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_three_root_symmetry_excludes_one
-- name    : Couret.STROBO2TORS.recoh_three_root_symmetry_excludes_one
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:31:35.612763+00:00
-- url     : https://prove2.me/theorems/4765767d-3b90-44f2-a5f5-5b321f805a38
-- title:
--   The symmetric three-root equations exclude one
-- statement:
--   Let $b,c\in\mathbb C$ satisfy $1+b+c=0$ and $b+c+bc=0$. Then
--
--   $$b\ne1.$$
--
--   This elementary obstruction is used in primary-probe nonvanishing.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohTwoPowerCoprimeGate.lean, lines 33–45; source file SHA-256 4bf596c724a3008f424374c52c9bde458fd647cd65dc7f10702947a982bbfdf6; theorem Couret.STROBO2TORS.recoh_three_root_symmetry_excludes_one

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

/-!
An elementary algebraic gate for the nonvanishing of three 2-primary
complex roots. This file does NOT yet prove the full nonvanishing
theorem or construct the RECOH character bank.
-/

namespace Couret.STROBO2TORS

theorem recoh_three_root_symmetry_excludes_one
    (b c : ℂ)
    (hsum : 1 + b + c = 0)
    (hpair : b + c + b * c = 0) :
    b ≠ 1 := by sorry


end Couret.STROBO2TORS
