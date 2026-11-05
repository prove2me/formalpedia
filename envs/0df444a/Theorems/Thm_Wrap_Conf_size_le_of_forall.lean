-- Prove2me | Theorems.Thm_Wrap_Conf_size_le_of_forall
-- name    : Wrap.Conf.size_le_of_forall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:03:17.545226+00:00
-- url     : https://prove2.me/theorems/4b06c35d-206d-4edf-a8da-dff52dd9be1b
-- title:
--   Conf: size le of forall
-- statement:
--   A list whose entries have size at most B has size at most (number of entries)·(B + 1) + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L65-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L65-L75

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
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Wrap Wrap.Conf
open Turing Groundwork CircuitLowerBound.Tab

theorem Wrap.Conf.size_le_of_forall {α : Type} [HasSize α] {l : List α} {B : ℕ} (h : ∀ x ∈ l, size x ≤ B) :
    size l ≤ l.length * (B + 1) + 1 := by sorry
