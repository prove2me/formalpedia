-- Prove2me | Theorems.Thm_Wrap_Conf_size_map_le
-- name    : Wrap.Conf.size_map_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:22:08.873419+00:00
-- url     : https://prove2.me/theorems/80082e9d-c716-480a-b6f1-abe74307596d
-- title:
--   Conf: size map le
-- statement:
--   If every entry grows by at most e, the list grows by at most (number of entries)·e.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L78-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L78-L88

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Coding
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Definitions.Def_ToTuring_Lib_Table
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Nat1
import Mathlib.Data.Finite.Sigma
import Mathlib.Tactic.Linarith
import Definitions.Def_Wrap_CodingExists
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open Wrap Wrap.Conf
open Turing Groundwork CircuitLowerBound.Tab

theorem Wrap.Conf.size_map_le {ι α : Type} [HasSize α] (ks : List ι) (f g : ι → α) (e : ℕ) (h : ∀ k ∈ ks, size (f k) ≤ size (g k) + e) :
    size (ks.map f) ≤ size (ks.map g) + ks.length * e := by sorry
