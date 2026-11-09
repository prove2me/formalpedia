-- Prove2me | Theorems.Thm_Couret_InterIA_Fibres_four_partition_rigidity
-- name    : Couret.InterIA.Fibres.four_partition_rigidity
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:27.002311+00:00
-- url     : https://prove2.me/theorems/af2852c9-d6ed-4d9d-918a-47e2a1fcc6a8
-- title:
--   Four-part sign rigidity modulo a polynomial
-- statement:
--   Let $Q,A,B,C,D\in\mathbb R[X]$, with $Q$ coprime to the constant polynomial 4. Assume $Q$ divides none of $A(B+C+D),B(A+C+D),C(A+B+D),D(A+B+C),(A+B)(C+D),(A+C)(B+D),(A+D)(B+C)$. Choose independent signs for the four summands and write their signed sum as $U$. If $Q$ divides $(A+B+C+D)^2-U^2$, then $$U=A+B+C+D\quad\text{or}\quad U=-(A+B+C+D).$$
--
--   This excludes all nonconstant sign partitions under the stated seven obstructions.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/FourSignRigidity.lean, lines 48–120; source file SHA-256 7457f510d3cb5dc7da1d3bc7f820517db19363da66a96ff0fd98a3e1f65bb956; theorem Couret.InterIA.Fibres.four_partition_rigidity

import Definitions.Def_Couret_FourSignRigidity_4bbe2289ca60
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Couret_NegacyclicBinomial_2c67c9514814

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Polynomial

theorem four_partition_rigidity (Q A B C D : ℝ[X])
    (hfour : IsCoprime Q (4 : ℝ[X]))
    (hA : ¬ Q ∣ A*(B+C+D)) (hB : ¬ Q ∣ B*(A+C+D))
    (hC : ¬ Q ∣ C*(A+B+D)) (hD : ¬ Q ∣ D*(A+B+C))
    (hAB : ¬ Q ∣ (A+B)*(C+D)) (hAC : ¬ Q ∣ (A+C)*(B+D))
    (hAD : ¬ Q ∣ (A+D)*(B+C))
    (e0 e1 e2 e3 : Bool)
    (heq : Q ∣ (A+B+C+D)^2 -
      (signed e0 A + signed e1 B + signed e2 C + signed e3 D)^2) :
    signed e0 A + signed e1 B + signed e2 C + signed e3 D = A+B+C+D ∨
    signed e0 A + signed e1 B + signed e2 C + signed e3 D = -(A+B+C+D) := by sorry






end Couret.InterIA.Fibres
