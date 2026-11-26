-- Prove2me | Theorems.Thm_section5_grid_exp_sum
-- name    : section5_grid_exp_sum
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:57:54.111503+00:00
-- url     : https://prove2.me/theorems/7d8d0013-fb58-4ce4-baed-53f2d4585fb8
-- title:
--   Equality of grid-indexed and bit-indexed Gaussian normalization sums
-- statement:
--   Let $n,q$ be natural numbers with $q>0$, and set $M=2^q$. Let $x_j\in\mathbb R^n$ be the tensor-grid node indexed by $j\in\{0,\ldots,M-1\}^n$, with scalar nodes $-\sqrt{4\pi/M}\,M/2+\sqrt{4\pi/M}j_i$. Let $g(z)$ be the grid point associated with an $nq$-bit register by the construction's bit-grid encoding, and write $W(z)=e^{-\|g(z)\|^2/2}$. Then
--
--   $$
--   \sum_{j\in\{0,\ldots,2^q-1\}^n}e^{-\|x_j\|^2/2}=\sum_{z\in\{0,1\}^{nq}}W(z).
--   $$
--
--   This identifies the Gaussian normalization sums under the two indexing conventions.
-- source:
--   Original auxiliary result supporting Section 5 of https://arxiv.org/html/2609.40331v3; not asserted to be a separately numbered result of the paper. Exact local source: Solutions/Section5GridPhaseMatchesQEX.lean, section5_grid_exp_sum, lines 102–117.

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
import Definitions.Def_QuantumLTF_Membership_splitReg
import Definitions.Def_Section5Verified_Section5GridIsometry
import Definitions.Def_Section5Verified_Section5GridPhaseMatchesQEX
import Definitions.Def_Section5Verified_Section5PhysicalHermiteGrid
import Mathlib
namespace «Aux_w_53_hermite»
end «Aux_w_53_hermite»
set_option autoImplicit false
open MeasureTheory QAlgorithms QuantumLTF.Example QuantumLTF.Membership Aux_w_53_hermite

theorem section5_grid_exp_sum {n q : ℕ} (hq : 0 < q) :
    (∑ j : Fin n → Fin (2^q),
      Real.exp (-‖(WithLp.toLp 2 (section5_grid_node n (2^q) j) : EuclideanSpace ℝ (Fin n))‖^2/2)) =
        ∑ z : Qubits (n*q), gridWeight z := by sorry
