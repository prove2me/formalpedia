-- Prove2me | Theorems.Thm_section5_classical_controlled_swap_register
-- name    : section5_classical_controlled_swap_register
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:47:04.879338+00:00
-- url     : https://prove2.me/theorems/e9da5a95-3c81-4482-8a10-85fa45166e8d
-- title:
--   Controlled swap of two registers
-- statement:
--   For every natural w, two w-bit registers can be swapped conditional on one control bit by a reversible circuit on 1+2w wires: $$|c,a,b\rangle\mapsto\begin{cases}|c,b,a\rangle&c=1,\\|c,a,b\rangle&c=0,\end{cases}\qquad|C|\le7w.$$
-- source:
--   Original auxiliary result supporting Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5; this metadata does not claim the paper states this auxiliary lemma verbatim. Exact formalization: Solutions/Section5ControlledSelection.lean, lines 33–35. Arithmetic dependencies reuse Robin Kothari’s accepted proof, Prove2Me submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), in Solutions/Section5LcgArithmeticFoundation.lean; that copied foundation is not a new contribution.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5ClassicalArithmeticRealization
import Definitions.Def_Section5Verified_Section5ClassicalGateFoundation
import Definitions.Def_Section5Verified_Section5LcgArithmeticFoundation
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
import Theorems.Thm_Aux_w54_arith_cswapRegCircuit_implements
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

theorem section5_classical_controlled_swap_register (w : ℕ) :
    ∃ c : Circuit gatesRev (1+w+w), c.size ≤ 7*w ∧
      ∀ z : Qubits (1+w+w), act c.unitary (ket z)=ket (cswapRegFn w z) := by sorry
