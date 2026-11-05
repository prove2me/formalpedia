-- Prove2me | Theorems.Thm_Wrap_Conf_polyT_map_const
-- name    : Wrap.Conf.polyT_map_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:21:52.035861+00:00
-- url     : https://prove2.me/theorems/ff883ac4-fe22-4eb8-a840-189b6bbb44e5
-- title:
--   Conf: poly T map const
-- statement:
--   A fixed list of polynomial-time functions, applied to one argument, is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L91-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/CodingExists.lean#L91-L95

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
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open Wrap Wrap.Conf
open Turing Groundwork CircuitLowerBound.Tab

theorem Wrap.Conf.polyT_map_const {ι α β : Type} [Enc α] [Enc β] (l : List ι) (g : ι → α → β) (h : ∀ i, PolyT (g i)) :
    PolyT fun x => l.map fun i => g i x := by sorry
