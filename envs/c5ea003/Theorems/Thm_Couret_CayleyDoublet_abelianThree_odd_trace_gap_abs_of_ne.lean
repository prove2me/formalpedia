-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianThree_odd_trace_gap_abs_of_ne
-- name    : Couret.CayleyDoublet.abelianThree_odd_trace_gap_abs_of_ne
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:31:29.108651+00:00
-- url     : https://prove2.me/theorems/48f6b805-bb26-4556-8627-4df274a36299
-- title:
--   Exact nonzero odd-trace gap magnitude
-- statement:
--   Let G be a finite abelian group, a,d,h in G, 2h=0 and h≠0. Put Q=G/<h>, S={a,a+d,a+d+h}, T={a,a-d,a-d+h}, A the rational directed Cayley adjacency matrix of S and B that of T, including any loops. Assume the image of d in Q has additive order exactly three. For any natural n, if tr(A^(2n+1))≠tr(B^(2n+1)), then $$|\operatorname{tr}(A^{2n+1})-\operatorname{tr}(B^{2n+1})|=|G|3^n.$$ No generation or odd-quotient-cardinality assumption is required for this conditional gap formula.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/1483e8ae3e5491ee176364fe944c90c4341d40ff/research/correspondants_20261013/lean/CayleyTwoColourFirstCoeff.lean#L109-L156, lines 109–156; source file SHA-256 e45556611be08e80f77ef2e9b917f78da4477576677474f9c2ab22aad4727fd9; theorem Couret.CayleyDoublet.abelianThree_odd_trace_gap_abs_of_ne

import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_odd_trace_sub
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f

/-!
COU-20: the first differing characteristic-polynomial coefficient.

The original spectral equivalence and first-trace certificates are imported
unchanged. We reuse the previously proved finite Newton prefix identities,
the generic single-matrix Newton theorem, and the canonical odd quotient
return. All statements refer to the actual rational directed adjacency
matrices (including their loops).

The numerical absolute-gap formula remains a documented mathematical
corollary, not a claim of formalization in this file.
-/

set_option autoImplicit false
noncomputable section

namespace Couret.CayleyDoublet

open Couret.CayleyNewton

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem abelianThree_odd_trace_gap_abs_of_ne
    (a d h : G)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (horder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3)
    (n : ℕ)
    (hdiff : Matrix.trace
      (abelianCayleyMatrix (AbelianSource a d h) ^ (2 * n + 1)) ≠
      Matrix.trace (abelianCayleyMatrix (AbelianTarget a d h) ^ (2 * n + 1))) :
    |Matrix.trace (abelianCayleyMatrix (AbelianSource a d h) ^ (2 * n + 1)) -
      Matrix.trace (abelianCayleyMatrix (AbelianTarget a d h) ^ (2 * n + 1))| =
      (Fintype.card G : ℚ) * (3 : ℚ) ^ n := by sorry







end Couret.CayleyDoublet
