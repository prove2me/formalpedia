-- Prove2me | Theorems.Thm_section5_boolean_list_compile
-- name    : section5_boolean_list_compile
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:04:19.828718+00:00
-- url     : https://prove2.me/theorems/980ce06a-356c-4c9a-8d89-705253d54abb
-- title:
--   Linear-size reversible compilation of a Boolean gate list
-- statement:
--   Let L be a Boolean straight-line program with r gates and p input bits. Assume p+r≤m and that gate k reads its first input at an index below p+k, and, unless it is negation, also reads its second input below p+k. There exists a reversible m-wire circuit C such that for every input list v of length p, initially filling all other wires with zero,
--
--   $$U_C|\operatorname{memory}_m(v)\rangle=|\operatorname{memory}_m(\operatorname{values}_L(v))\rangle,\qquad |C|\le3r.$$
--
--   Here values appends each gate's Boolean output to the input list in order; memory pads a list with false bits. The input and all intermediate outputs are retained.
-- source:
--   Original auxiliary Boolean compilation result supporting Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5BooleanCircuitCompilation.lean, lines 33–41; memory and sequential-value definitions, lines 9–10 and 30–31.

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_Section5Verified_Section5BooleanCircuitCompilation
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
import Theorems.Thm_section5_boolean_gate_action
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership

theorem section5_boolean_list_compile (l : List BoolGate) (m p : ℕ)
    (hspace : p+l.length ≤ m)
    (hwf : ∀ k (hk : k < l.length),
      (l[k]).a < p+k ∧ ((l[k]).op=BoolOp.not ∨ (l[k]).b < p+k)) :
    ∃ c : Circuit gatesRev m, c.size ≤ 3*l.length ∧
      ∀ v : List Bool, v.length=p →
        act c.unitary (ket (section5_boolean_memory m v))=
          ket (section5_boolean_memory m (section5_boolean_values l v)) := by sorry
