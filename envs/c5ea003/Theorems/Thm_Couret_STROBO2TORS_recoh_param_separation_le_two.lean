-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_param_separation_le_two
-- name    : Couret.STROBO2TORS.recoh_param_separation_le_two
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:55:52.572119+00:00
-- url     : https://prove2.me/theorems/aee1e3bd-facb-409c-b604-030cb35ba321
-- title:
--   No character bank separates an exceptional fibre by more than two
-- statement:
--   Let $G$ be an abelian group, $P_\chi(A)=\sum_{x\in A}\chi(x)$, $R_A(z)$ the ordered pair-sum count, $F(A)$ the full fibre among three-element supports, and $H=G[2]$. Assume $G$ finite. Let $a,d,v\in G$ satisfy $d\ne0$, $2d=0$, $v\ne0$, $3v=0$, and put $A=\{a,a+v,a+v+d\}$. A bank is $\delta$-separated on a candidate set when every two distinct candidates have at least one reading whose distance is at least $\delta$. For any bank indexed by any type and any real $\delta$,
--
--   $$\delta\text{-separation on }F(A)\Longrightarrow\delta\le2.$$
--
--   There is no bound on the number of bank slots.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohExceptionalStability.lean#L215-L239, lines 215–239; source file SHA-256 788e929f7e526870f55ea3a771c8f7f5dc647bcd18b0afb61c80f3eaf4f4c947; theorem Couret.STROBO2TORS.recoh_param_separation_le_two

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_opposite_probe_distance
import Theorems.Thm_Couret_STROBO2TORS_recoh_support_probe_three
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_torsion_probe_is_sign
import Theorems.Thm_Couret_STROBO2TORS_torsionOrbit_subset_fibre
import Theorems.Thm_Couret_STROBO2TORS_translateSupport_free_of_card_three
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

theorem recoh_param_separation_le_two
    {I : Type*} (bank : I → AddChar G ℂ) (a d v : G)
    (hd : d + d = 0) (hd0 : d ≠ 0)
    (hv : (v + v) + v = 0) (hv0 : v ≠ 0)
    (δ : ℝ) (hsep : RecohProbeSeparated bank
      (squareFibre (paramSupport ((a, d), v))) δ) : δ ≤ 2 := by sorry




end Couret.STROBO2TORS
