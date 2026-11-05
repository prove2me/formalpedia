-- Prove2me | Theorems.Thm_Wrap_decidesTM_of_wraps_counter
-- name    : Wrap.decidesTM_of_wraps_counter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:38:43.6336+00:00
-- url     : https://prove2.me/theorems/e5bc9989-3092-4691-9f41-530bf9ffd910
-- title:
--   Wrap: decides TM of wraps counter
-- statement:
--   A wrapper N of a machine M that counts on the compact code within the bound, with «some bit is
--   1» after it, decides 3-SAT on the plain code within every time bound T that `Covers` allows.
--   M is used at width 3; the count of `pad4 φ`, written in binary, has a bit 1 if and only if `pad4 φ`
--   is satisfiable. At width 3 the bound with the constant C is at most the bound for width 3 with the
--   constant 9·C.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Main.lean#L57-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/Wrap/Main.lean#L57-L71

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Defs
import Definitions.Def_Wrap_CodingExists
import Definitions.Def_Wrap_Sim
import Definitions.Def_Wrap_FrontEnd
import Definitions.Def_Wrap_Arith
import Definitions.Def_Wrap_ArithRate
import Definitions.Def_WidthThree_Rates
import Definitions.Def_VariableBound_Paper_MainTheorem
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_Rename_End
import Definitions.Def_Wrap_Main
import Theorems.Thm_ClauseBound_Inst_Half_CertSmall_d
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Wrap
open Turing Groundwork
open scoped NNReal

theorem Wrap.decidesTM_of_wraps_counter {pre : List Bool → List Bool} (hpre : MapsPlainToPaddedCompact pre) {M : TM2ComputableAux Bool Bool} {C : ℕ} (hM : CountsCompactKCNFWithinMinBound M C)
    {N : TM2ComputableAux Bool Bool} {q : ℕ} (hW : Wraps M pre someBit N q) {a d : ℕ}
    (hL : ∀ (n : ℕ) (φ : Sat3.CNF n), Sat3.Is3CNF φ → (MainTheoremForms.encC 3 (pad4 φ)).length ≤ a * (n + 2) ^ d ∧ (Sat3.enc φ).length ≤ a * (n + 2) ^ d)
    {T : ℕ → ℕ} (hT : Covers q (9 * C) C a d T) : Sat3.DecidesTM N T := by sorry
