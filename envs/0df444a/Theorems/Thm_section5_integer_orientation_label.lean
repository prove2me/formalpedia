-- Prove2me | Theorems.Thm_section5_integer_orientation_label
-- name    : section5_integer_orientation_label
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:55:14.485969+00:00
-- url     : https://prove2.me/theorems/8599018f-ac86-4837-872f-2c6f07e256d3
-- title:
--   Fixed-point grid classification is an integer sign test
-- statement:
--   Let $n,q,f\in\mathbb N$ and $\ell\ge1$. Let $u_i$ be $\ell$-bit most-significant-bit-first strings, and let $x$ concatenate $n$ strings $x_i$ of $q$ bits. For an $r$-bit string $z$, put $J_r(z)=N(z)-2^{r\mathbin{\dot-}1}$, where $N$ is its unsigned value and $\dot-$ is subtraction truncated at zero. Define fixed-point coordinates $v_i=J_\ell(u_i)/2^f$, and let $g(x)$ be the public centered grid point. With $\operatorname{sgn}(0)=1$,
--
--   $$\operatorname{sgn}\langle v,g(x)\rangle=\operatorname{sgn}\!\left(\sum_iJ_\ell(u_i)J_q(x_i)\right).$$
--
--   This reduces the fixed-point orientation label to an exact centered-integer dot-product sign test.
-- source:
--   Original encoding identity for Section 5 orientation in Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3. Formalization: Solutions/Section5IntegerOrientation.lean, lines 57–66. Offset-binary fixed-point convention: Definitions/Def_QuantumLTF_Membership_fpVal.lean.

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Gates
import Definitions.Def_QuantumLTF_Example_HermiteModel
import Definitions.Def_QuantumLTF_Example_qex
import Definitions.Def_QuantumLTF_Membership_Supplement_band1D53
import Definitions.Def_QuantumLTF_Membership_Supplement_bandKet
import Definitions.Def_QuantumLTF_Membership_Supplement_bandWeight
import Definitions.Def_QuantumLTF_Membership_Supplement_hermCoeff
import Definitions.Def_QuantumLTF_Membership_Supplement_projDist
import Definitions.Def_QuantumLTF_Membership_flatReg
import Definitions.Def_QuantumLTF_Membership_fpVal
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5GridIsometry
import Definitions.Def_Section5Verified_Section5GridPhaseMatchesQEX
import Definitions.Def_Section5Verified_Section5IntegerOrientation
import Mathlib
set_option autoImplicit false
open QAlgorithms QuantumLTF.Example QuantumLTF.Membership

theorem section5_integer_orientation_label {n q ℓ : ℕ} (hℓ : 0 < ℓ) (f : ℕ)
    (u : Fin n → Qubits ℓ) (x : Qubits (n*q)) :
    ltf (WithLp.toLp 2 (fun i => fpVal ℓ f (u i))) 0 (gridPoint x) =
      sgn (section5_integer_orientation_dot u x : ℝ) := by sorry
