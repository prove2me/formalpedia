-- Prove2me | Theorems.Thm_Couret_CayleyDoublet_abelianThree_noncospectral_of_generated_odd_quotient
-- name    : Couret.CayleyDoublet.abelianThree_noncospectral_of_generated_odd_quotient
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:48:20.531473+00:00
-- url     : https://prove2.me/theorems/0feb1075-66a0-48b4-8412-b3bb1fb6c48d
-- title:
--   Generated odd quotient gives noncospectrality
-- statement:
--   Let G be a finite abelian group, a,d,h in G, 2h=0 and h≠0. Put Q=G/<h>, S={a,a+d,a+d+h}, T={a,a-d,a-d+h}, A the rational directed Cayley adjacency matrix of S and B that of T, including any loops. Assume the image of d in Q has additive order exactly three. If <a,h>=G and |Q| is odd, then $$\operatorname{charpoly}(A)\ne\operatorname{charpoly}(B).$$ No separate generation-by-a,d,h premise is required.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/1483e8ae3e5491ee176364fe944c90c4341d40ff/research/correspondants_20261013/lean/CayleyTwoColourClassification.lean#L90-L105, lines 90–105; source file SHA-256 d5e3fa101ab825c87b19dceead2d61cb5de3cf4986d44637cad46caf7831ac24; theorem Couret.CayleyDoublet.abelianThree_noncospectral_of_generated_odd_quotient

import Definitions.Def_Couret_CayleyCharpolyTrace_5d18cab1d32f
import Definitions.Def_Couret_CayleyTwoColourNewton_1eb4b626b6a5
import Mathlib
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Theorems.Thm_Couret_CayleyDoublet_abelianThree_odd_trace_witness_of_odd_quotient
import Theorems.Thm_Couret_CharpolyTrace_trace_pow_eq_of_charpoly_eq
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

theorem abelianThree_noncospectral_of_generated_odd_quotient
    (a d h : G)
    (hhalf : h + h = 0) (hne : h ≠ 0)
    (horder : addOrderOf (d : G ⧸ AddSubgroup.zmultiples h) = 3)
    (hpair : AddSubgroup.closure ({a, h} : Set G) = ⊤)
    (hodd : Odd (Nat.card (G ⧸ AddSubgroup.zmultiples h))) :
    (abelianCayleyMatrix (AbelianSource a d h)).charpoly ≠
      (abelianCayleyMatrix (AbelianTarget a d h)).charpoly := by sorry


end Couret.CayleyDoublet
