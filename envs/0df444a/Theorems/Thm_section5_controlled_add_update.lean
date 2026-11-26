-- Prove2me | Theorems.Thm_section5_controlled_add_update
-- name    : section5_controlled_add_update
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:46:06.610474+00:00
-- url     : https://prove2.me/theorems/71acf503-c108-5f77-8b1f-3c98153501e3
-- title:
--   Payload-only form of an embedded controlled addition
-- statement:
--   Let $p$ embed $w$ payload wires into an $m$-bit register, and let a control wire $c$ be distinct from every payload wire. Let $a\in\mathbb N$ and $z\in\{0,1\}^m$. Apply the specified controlled constant-adder basis function to the embedded control and payload. If $B$ is the least-significant-bit-first unsigned value of $z\circ p$, the resulting ambient string is
--
--   $$F_a(z)=\begin{cases}z[p\leftarrow\operatorname{bits}_w((a\bmod2^w)+B)],&z_c=1,\\z,&z_c=0.\end{cases}$$
--
--   Here $\operatorname{bits}_w$ retains the low $w$ bits. The identity exposes that the control and every nonpayload wire are unchanged.
-- source:
--   Original embedded-update identity in Solutions/Section5EmbeddedClassicalArithmetic.lean, lines 56–111, for the Section 5 postprocessing of Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3. The controlled-adder basis function comes from Robin Kothari's accepted arithmetic submission 0ac99132-8635-4775-91de-dd0ad0e55353 (Apache-2.0), credited in Solutions/Section5LcgArithmeticFoundation.lean.

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
import Definitions.Def_Section5Verified_Section5EmbeddedClassicalArithmetic
import Definitions.Def_Section5Verified_Section5LcgArithmeticFoundation
import Definitions.Def_Section5Verified_Section5ReversibleBooleanCompiler
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Membership Thm49Primitives Thm410Router
open QuantumLTF.Membership.Supplement.LcgSym54

theorem section5_controlled_add_update {m w : ℕ} (a : ℕ) (ctrl : Fin m) (p : Fin w ↪ Fin m)
    (hc : ∀ i, ctrl ≠ p i) (z : Qubits m) :
    updateOn (section5_control_payload_embedding ctrl p hc) z
      (Aux_w54_arith.ctrlAddConstInPlaceFn w a (z ∘ section5_control_payload_embedding ctrl p hc)) =
    if z ctrl then updateOn p z (natToBitsLSB w (a % 2^w+bitsToNatLSB (z ∘ p))) else z := by sorry
