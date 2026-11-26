-- Prove2me | Theorems.Thm_section5_boolCircuit_reversible_compile
-- name    : section5_boolCircuit_reversible_compile
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T20:07:44.761853+00:00
-- url     : https://prove2.me/theorems/c5d0360a-2328-5f3b-a229-9031b3361dba
-- title:
--   Linear-size reversible realization of a Boolean circuit
-- statement:
--   Let $C$ be a well-formed Boolean straight-line circuit with $n$ input bits, $r$ output bits, and $s$ gates. Well-formedness means that each gate reads available earlier wires and each output names a valid wire. There exist a NOT/CNOT/Toffoli circuit $R$ on $n+s$ wires and output positions $o_1,\ldots,o_r$ such that, for every input $x$, some final basis string $z$ satisfies
--
--   $$|R|\le3s,\qquad U_R|x,0^s\rangle=|z\rangle,\qquad z_{o_j}=C(x)_j\quad(1\le j\le r).$$
--
--   This realizes the Boolean output with a linear number of reversible gates and initialized workspace; the statement permits intermediate values to remain in that workspace.
-- source:
--   Original Boolean-to-reversible compilation result for the Section 5 classical postprocessing of Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3. Formalization: Solutions/Section5BooleanCircuitCompilation.lean, lines 88–118.

import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_Section5Verified_Section5BooleanCircuitCompilation
import Mathlib
import Theorems.Thm_section5_boolean_list_compile
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership

theorem section5_boolCircuit_reversible_compile {n r : ℕ} (C : BoolCircuit n r) (hC : C.WellFormed) :
    ∃ (c : Circuit gatesRev (n+C.size)) (out : Fin r → Fin (n+C.size)),
      c.size ≤ 3*C.size ∧
      ∀ x : Qubits n, ∃ z : Qubits (n+C.size),
        act c.unitary (ket (Fin.append x (fun _ : Fin C.size => false)))=ket z ∧
          ∀ j, z (out j)=C.eval x j := by sorry
