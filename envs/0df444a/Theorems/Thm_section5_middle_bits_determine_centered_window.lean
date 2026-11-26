-- Prove2me | Theorems.Thm_section5_middle_bits_determine_centered_window
-- name    : section5_middle_bits_determine_centered_window
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:53:06.645612+00:00
-- url     : https://prove2.me/theorems/83e6227d-6e84-48be-8c0b-cd534e0e305a
-- title:
--   Middle bits determine the centered signed window
-- statement:
--   Let $z,y$ be most-significant-bit-first $q$-bit strings, let $s,b\in\mathbb N$ satisfy $s+b\le q-1$, and let $H\in\mathbb Z$ satisfy $2^b=2H$. Suppose that $z$ and $y$ have the same bits in unsigned significance positions $s,\ldots,s+b-1$. Put $J(z)=N(z)-2^{q-1}$ and $W_{P,H}(k)=P\operatorname{sres}_H(\lfloor k/P\rfloor)$, with signed representatives in $[-H,H)$. Then
--
--   $$W_{2^s,H}(J(z))=W_{2^s,H}(J(y)).$$
--
--   This shows that the selected middle wires completely determine the centered window despite omission of the other bits.
-- source:
--   Original bit-window encoding auxiliary result for Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5. Formalization: Solutions/Section5MiddleBits.lean, lines 68–76.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_bitonicTrace54
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_lcgSym54ArithV2
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_Supplement_symBand54
import Definitions.Def_QuantumLTF_Membership_Supplement_thm410_router_blocks
import Definitions.Def_QuantumLTF_Membership_Supplement_thm49_primitives
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5IntegerOrientation
import Definitions.Def_Section5Verified_Section5MiddleBits
import Definitions.Def_Section5Verified_Section5SignedWindow
import Mathlib
set_option autoImplicit false
open QAlgorithms Thm49Primitives

theorem section5_middle_bits_determine_centered_window {q : ℕ}
    (z y : Qubits q) (s b : ℕ) (h : s+b ≤ q-1) (H : ℤ)
    (hb : (2:ℤ)^b=2*H)
    (heq : section5_middle_bits z s b (by omega)=section5_middle_bits y s b (by omega)) :
    section5_window_truncate ((2:ℤ)^s) H (section5_centered_integer z)=
      section5_window_truncate ((2:ℤ)^s) H (section5_centered_integer y) := by sorry
