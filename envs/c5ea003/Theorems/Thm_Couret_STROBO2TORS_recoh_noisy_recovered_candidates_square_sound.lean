-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_noisy_recovered_candidates_square_sound
-- name    : Couret.STROBO2TORS.recoh_noisy_recovered_candidates_square_sound
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:17:31.135522+00:00
-- url     : https://prove2.me/theorems/a7665ae4-cf06-4c3f-867a-12392673b9d2
-- title:
--   Recovered candidates stay in the exact square fibre
-- statement:
--   For a rational pair z=(a,b), write V(z)=a+bi. Let G be an abelian group, H=G[2], and P_i(B)=sum_(x in B)chi_i(x) for a bank of complex additive characters. An additive equivalence e:H≃(J→F_2) supplies binary coordinates. The rational sign test accepts exactly when the radius r is nonnegative and the rational squared distance from observed to predicted is at most r^2. Recovery translates each representative by the H-element obtained from its sign bits via e inverse. Assume G finite. For any finite reference support S, let F(S) be its square fibre among three-element supports, and let a finite representative family R satisfy R⊆F(S). For arbitrary e, predictions b, observations o and rational radius r, $$C(R,e,b,o,r)\subseteq F(S).$$ No sign-correctness, nonnegative-radius or error hypotheses are needed.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohNoisySignRecovery.lean#L158-L178, lines 158–178; source file SHA-256 0b99604778196eef3e1a2e7f4520b571c7f705ced9a9268c1833a15086c9a9a4; theorem Couret.STROBO2TORS.recoh_noisy_recovered_candidates_square_sound

import Aesop
import Definitions.Def_Couret_RecohNoisySignRecovery_25d41afc9bfe
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
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
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohNoisyUniqueness_7e21ca0c53e8
import Definitions.Def_Couret_RecohIndexedSignRecovery_d641979954b3

set_option autoImplicit false

/-!
Noisy sign recovery from a list of square-fibre representatives.  Each
binary sign is recovered by one rational ball test, then transported through
the existing two-torsion coordinate equivalence.  At most one candidate is
created per representative, without enumerating the two-torsion subgroup.
The rational decoder in RecohNoisyUniqueness supplies the final tolerance
filter and uniqueness contract.
-/

namespace Couret.STROBO2TORS







variable {G J : Type*} [AddCommGroup G] [DecidableEq G]

local notation "H₂" => recohTorsionSubgroup (G := G) 2

theorem recoh_noisy_recovered_candidates_square_sound [Fintype G]
    (S : Finset G) (representatives : Finset (Finset G))
    (hrepresentatives : representatives ⊆ squareFibre S)
    (e : H₂ ≃+ (J → ZMod 2))
    (predicted : Finset G → J → RecohRationalComplex)
    (observed : J → RecohRationalComplex) (radius : ℚ) :
    recohNoisyRecoveredCandidates representatives e predicted observed radius ⊆ squareFibre S := by sorry










end Couret.STROBO2TORS
