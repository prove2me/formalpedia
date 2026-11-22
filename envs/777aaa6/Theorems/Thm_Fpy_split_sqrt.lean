-- Prove2me | Theorems.Thm_Fpy_split_sqrt
-- name    : Fpy.split_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T06:38:25.413522+00:00
-- url     : https://prove2.me/theorems/bb82c6a5-6376-41cf-a554-cf5afc8220fa
-- title:
--   Fpy: split sqrt
-- statement:
--   Split's condition for `√` from Roux's rules (`rndSqrt_*`), when `F₂` is
--   unbounded.
--
--   Source: https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L379-L393
-- source:
--   https://github.com/bksaiki/mpfx-lean/blob/5085537ae18450579719a16ac4808b20472de1f3/Fpy/Rewrite/Separate.lean#L379-L393

import Definitions.Def_Fpy_Rewrite_Basic
import Definitions.Def_Fpy_FormatInference_Domain
import Definitions.Def_Mpfx_DoubleRounding_Special
import Definitions.Def_Fpy_Rewrite_Separate
set_option autoImplicit true
open Fpy
open Mpfx
variable {L : Signature} {D : FormatDomain} {Φ : Program L} {X : Set Var}
variable {A : Analysis L D}
variable {decode : List (Label × Val) → Option RoundCtx}
variable {c₁ c₂ : RoundCtx} (hS : c₂.S.Composes c₁.S c₁.O c₁.rm) (hb : c₂.F.b = ⊤)
include hS hb

theorem Fpy.split_sqrt
    (hrule : ∀ {a : Mpfx.Dyadic}, a ∈ c₁.F → 0 ≤ (a : ℝ) → ∀ {z w : Mpfx.Dyadic},
      RoundsFinite c₂.F.unbounded c₂.rm (Real.sqrt (a : ℝ)) z →
      RoundsFinite c₁.F.unbounded c₁.rm (z : ℝ) w →
      RoundsFinite c₁.F.unbounded c₁.rm (Real.sqrt (a : ℝ)) w)
    (us : List Num) (n : Num) (hus : ∀ u ∈ us, u ∈ c₁.F.reals)
    (hop : (fpy decode).arith (show ArithOp from .sqrt) us = some n) :
    c₁.round (c₂.round n) = c₁.round n := by sorry
