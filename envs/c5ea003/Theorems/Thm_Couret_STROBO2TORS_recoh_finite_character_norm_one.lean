-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_finite_character_norm_one
-- name    : Couret.STROBO2TORS.recoh_finite_character_norm_one
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:49:40.418399+00:00
-- url     : https://prove2.me/theorems/8f5ee97b-bcda-411c-9d9a-81884d5e0b81
-- title:
--   Characters of a finite group are unitary
-- statement:
--   Let G be an abelian group, S finite supports, chi complex additive characters, P_chi(S)=sum_(x in S)chi(x), and H={u:2u=0}. An H-orbit is {S+u:u in H}. A bank is delta-separated on a finite candidate family if every two distinct candidates have some coordinate whose probe difference has norm at least delta. Assume G finite. For every complex additive character chi and x in G, $$\|\chi(x)\|=1.$$ No support or nontrivial-character condition is required.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohProbeStability.lean#L38-L44, lines 38–44; source file SHA-256 1d695a0d84e83ff92491e95ea472df8f9bf1059d52c5525c794d82c7f31a9800; theorem Couret.STROBO2TORS.recoh_finite_character_norm_one

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
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883
import Definitions.Def_Couret_RecohFourierBridge_5b164a1abe76
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!
Quantitative separation of character readings.  A separation statement uses
an existential coordinate; no finite maximum, nonempty bank, or nontrivial
fibre is silently assumed.  In particular singleton fibres and empty banks
are handled by the same definition.
-/

namespace Couret.STROBO2TORS



variable {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in

theorem recoh_finite_character_norm_one [Fintype G]
    (chi : AddChar G ℂ) (x : G) : ‖chi x‖ = 1 := by sorry








variable [Fintype G]















end Couret.STROBO2TORS
