-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_exceptional_probe_distance_of_ne
-- name    : Couret.STROBO2TORS.recoh_exceptional_probe_distance_of_ne
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:57:48.935325+00:00
-- url     : https://prove2.me/theorems/1767a93b-5a27-40a3-bc86-2e7a5507a8c8
-- title:
--   Every differing two-torsion-trivial exceptional reading has exact distance
-- statement:
--   Let $G$ be an abelian group, $P_\chi(A)=\sum_{x\in A}\chi(x)$, $R_A(z)$ the ordered pair-sum count, $F(A)$ the full fibre among three-element supports, and $H=G[2]$. Assume $G$ finite, $A,B$ exceptional partners, and $\chi(u)=1$ for every $u\in H$. If $P_\chi(A)\ne P_\chi(B)$, then
--
--   $$|P_\chi(A)-P_\chi(B)|=2\sqrt3.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohExceptionalStability.lean#L142-L162, lines 142–162; source file SHA-256 788e929f7e526870f55ea3a771c8f7f5dc647bcd18b0afb61c80f3eaf4f4c947; theorem Couret.STROBO2TORS.recoh_exceptional_probe_distance_of_ne

import Aesop
import Definitions.Def_Couret_RecohProbeStability_e389a2280f15
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_paramSupport_card
import Theorems.Thm_Couret_STROBO2TORS_recoh_exceptional_normal_form
import Theorems.Thm_Couret_STROBO2TORS_recoh_finite_character_norm_one
import Theorems.Thm_Couret_STROBO2TORS_recoh_opposite_probe_distance
import Theorems.Thm_Couret_STROBO2TORS_recoh_stability_cubic_reading_norm
import Theorems.Thm_Couret_STROBO2TORS_recoh_support_probe_three
import Theorems.Thm_Couret_STROBO2TORS_three_torsion_neg
import Definitions.Def_Couret_RecohProbeStability_e389a2280f15

set_option autoImplicit false

/-!
Exact separation constants in the exceptional normal form.  Binary probes
have amplitudes one or three, and a detecting ternary probe separates the
two orbits by exactly twice the square root of three.  The two-torsion pair
inside the normal form supplies a matching universal upper bound of two.
-/

namespace Couret.STROBO2TORS





variable {G : Type*} [AddCommGroup G] [DecidableEq G]





variable [Fintype G]

theorem recoh_exceptional_probe_distance_of_ne (chi : AddChar G ℂ)
    (S T : Finset G) (he : ExceptionalPartner S T)
    (htrivial : ∀ u : G, u + u = 0 → chi u = 1)
    (hne : recohSupportProbe chi S ≠ recohSupportProbe chi T) :
    ‖recohSupportProbe chi S - recohSupportProbe chi T‖ = 2 * Real.sqrt 3 := by sorry










end Couret.STROBO2TORS
