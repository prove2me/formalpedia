-- Prove2me | Theorems.Thm_section5_window_precision_bounds
-- name    : section5_window_precision_bounds
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:06:34.135799+00:00
-- url     : https://prove2.me/theorems/9aff177d-97dc-4e1e-ae8c-b26088140d32
-- title:
--   Explicit bounds for the dimension-dependent window precision
-- statement:
--   Let n≥1 be natural and let B=clog₂(65536n), the least natural exponent for which 65536n≤2^B. Then
--
--   $$65536n\le2^B<131072n,\qquad B\le n+16.$$
-- source:
--   Original auxiliary parameter bound supporting Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5. Exact formalization: Solutions/Section5BoundedWindow.lean, lines 52–55; window precision definition, line 50.

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
import Definitions.Def_QuantumLTF_Membership_disagree
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_gatesRev
import Definitions.Def_QuantumLTF_Membership_ltf
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5BoundedWindow
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

theorem section5_window_precision_bounds (n : ℕ) (hn : 1 ≤ n) :
    65536*(n:ℝ) ≤ (2:ℝ)^(section5_window_precision n) ∧
      (2:ℝ)^(section5_window_precision n) < 131072*n ∧
      section5_window_precision n ≤ n+16 := by sorry
