-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianThree_first_trace_difference_at_quotient_third
-- name    : Couret.CayleyDoublet.abelianThree_first_trace_difference_at_quotient_third
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:37:15.473574+00:00
-- url     : https://prove2.me/theorems/b3ea0526-8134-4ac9-82a7-77145a7145a7
-- title:
--   First trace discrepancy at one third of the quotient size
-- statement:
--   Let G be a finite abelian group, a,d,h in G, 2h=0 and h≠0. Put Q=G/<h>, S={a,a+d,a+d+h}, T={a,a-d,a-d+h}, A the rational directed Cayley adjacency matrix of S and B that of T, including any loops. Assume the image of d in Q has additive order exactly three. Assume <a,h>=G and |Q| is odd. Put k=|Q|/3 using natural division. Then $$k>0,\quad k\text{ is odd},\quad\operatorname{tr}(A^j)=\operatorname{tr}(B^j)\ (0\le j<k),\quad\operatorname{tr}(A^k)\ne\operatorname{tr}(B^k).$$ This specifies the first differing degree, including equality at degree zero.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/1483e8ae3e5491ee176364fe944c90c4341d40ff/research/correspondants_20261013/lean/CayleyTwoColourClassification.lean#L24-L54, lines 24–54; source file SHA-256 d5e3fa101ab825c87b19dceead2d61cb5de3cf4986d44637cad46caf7831ac24; theorem Couret.CayleyDoublet.abelianThree_first_trace_difference_at_quotient_third

import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_canonical_odd_trace_difference
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_exists_canonical_odd_return
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_trace_eq_before_third
import Theorems.Thm_Couret_CayleyDoublet_quotient_alpha_order_of_pair_generation
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5

/-!
COU-20 — spectral necessity and classification for the directed triple pair.

The cyclic odd witness, exact odd-trace criterion, canonical third-period
return, and sufficient direction are reused without changing their modules.
The generic characteristic-polynomial-to-power-trace theorem discharges the
explicit bridge left open by the earlier conditional assembly.

Every adjacency matrix here is the existing directed Finset adjacency matrix.
No loop exclusion, undirected reinterpretation, or scientific novelty claim is
introduced. The coefficient-level Newton identities remain separate results.
-/

set_option autoImplicit false
noncomputable section

namespace Couret.CayleyDoublet

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem abelianThree_first_trace_difference_at_quotient_third
    (a d h : G)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (horder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3)
    (hpair : AddSubgroup.closure ({a, h} : Set G) = ⊤)
    (hodd : Odd (Nat.card (G ⧸ AddSubgroup.zmultiples h))) :
    let k := Nat.card (G ⧸ AddSubgroup.zmultiples h) / 3
    0 < k ∧ Odd k ∧
      (∀ j : ℕ, j < k →
        Matrix.trace (abelianCayleyMatrix (AbelianSource a d h) ^ j) =
          Matrix.trace (abelianCayleyMatrix (AbelianTarget a d h) ^ j)) ∧
      Matrix.trace (abelianCayleyMatrix (AbelianSource a d h) ^ k) ≠
        Matrix.trace (abelianCayleyMatrix (AbelianTarget a d h) ^ k) := by sorry








end Couret.CayleyDoublet
