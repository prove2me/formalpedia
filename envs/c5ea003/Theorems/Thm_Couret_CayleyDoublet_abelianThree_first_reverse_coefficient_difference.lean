-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianThree_first_reverse_coefficient_difference
-- name    : Couret.CayleyDoublet.abelianThree_first_reverse_coefficient_difference
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:48:45.255851+00:00
-- url     : https://prove2.me/theorems/60267606-8951-45b4-926b-5d8c15668b5b
-- title:
--   The canonical quotient third is the first reversed coefficient difference
-- statement:
--   Let $G$ be a finite abelian group, $h\ne0$ with $2h=0$, and $a,h$ generate $G$. Suppose $Q=G/\langle h\rangle$ has odd cardinality and $d+\langle h\rangle$ has order three. Write $A_+,A_-$ for the rational directed Cayley matrices of supports $\{a,a+d,a+d+h\}$ and $\{a,a-d,a-d+h\}$. Set $k=|Q|/3$ and use reversed coefficients, zero beyond matrix dimension. Then
--
--   $$c_+(j)=c_-(j)\ (0<j<k),\qquad c_+(k)\ne c_-(k).$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/bef25648f750d1b9d7792a883597021665e3ba00/research/correspondants_20261013/lean/CayleyTwoColourFirstCoefficient.lean#L75-L106, lines 75–106; source file SHA-256 f26de50d22cca32e5b50cae2954724a46bdbf8e8b8465f15443d7d7c8bb63e39; theorem Couret.CayleyDoublet.abelianThree_first_reverse_coefficient_difference

import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_first_trace_difference_at_quotient_third
import Theorems.Thm_Couret_CayleyNewton_first_reverse_coefficient_gap_of_first_trace_difference
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f

/-!
COU-20 — exact first characteristic coefficient obstruction.

RESEARCH CANDIDATE: must be compiled with the pinned Lean 4.29.1
toolchain and its #print axioms checked before a certification claim.

The general matrix theorem uses the now-proposed unconditional Newton
recurrence for rational square matrices. The directed Cayley corollary
uses the previously established first trace discrepancy at one third
of the odd quotient cardinality. No graph symmetry, loop exclusion,
new axiom, or independent generation assumption is introduced.
-/

set_option autoImplicit false
noncomputable section

open Matrix

namespace Couret.CayleyNewton

variable {i : Type*} [Fintype i] [DecidableEq i]



end Couret.CayleyNewton

namespace Couret.CayleyDoublet

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem abelianThree_first_reverse_coefficient_difference
    (a d h : G)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (horder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3)
    (hpair : AddSubgroup.closure ({a, h} : Set G) = ⊤)
    (hodd : Odd (Nat.card (G ⧸ AddSubgroup.zmultiples h))) :
    let k := Nat.card (G ⧸ AddSubgroup.zmultiples h) / 3
    (∀ j : ℕ, 0 < j → j < k →
      Couret.CayleyNewton.reverseCharpolyCoeff
        (abelianCayleyMatrix (AbelianSource a d h)) j =
      Couret.CayleyNewton.reverseCharpolyCoeff
        (abelianCayleyMatrix (AbelianTarget a d h)) j) ∧
    Couret.CayleyNewton.reverseCharpolyCoeff
      (abelianCayleyMatrix (AbelianSource a d h)) k ≠
    Couret.CayleyNewton.reverseCharpolyCoeff
      (abelianCayleyMatrix (AbelianTarget a d h)) k := by sorry


end Couret.CayleyDoublet
