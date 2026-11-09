-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_rational_sign_same_correct
-- name    : Couret.STROBO2TORS.recoh_rational_sign_same_correct
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:03:41.409946+00:00
-- url     : https://prove2.me/theorems/ab843376-0748-4ba0-8df3-ad5391e3bfa4
-- title:
--   The noisy sign test recovers the true sign
-- statement:
--   Let z be complex with ||z||≥1, b,o rational coordinate pairs, r≥0 rational, epsilon,eta real, and p a Boolean. Assume ||V(b)-z||≤eta and ||V(o)-(if p then z else -z)||≤epsilon, with $$\varepsilon+\eta\le r,\qquad\varepsilon+(r+\eta)<2.$$ Then $$\operatorname{Same}(b,o,r)=p.$$ No separately stated nonnegativity assumptions on epsilon or eta are added.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohNoisySignRecovery.lean#L33-L65, lines 33–65; source file SHA-256 0b99604778196eef3e1a2e7f4520b571c7f705ced9a9268c1833a15086c9a9a4; theorem Couret.STROBO2TORS.recoh_rational_sign_same_correct

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_noisy_prediction_sound
import Theorems.Thm_Couret_STROBO2TORS_recoh_opposite_probe_distance
import Theorems.Thm_Couret_STROBO2TORS_recoh_rational_ball_iff
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

theorem recoh_rational_sign_same_correct
    (truth : ℂ) (base observed : RecohRationalComplex) (radius : ℚ)
    (ε η : ℝ) (positive : Bool) (hradius : 0 ≤ radius)
    (hamplitude : 1 ≤ ‖truth‖)
    (hpred : ‖recohRationalComplexValue base - truth‖ ≤ η)
    (hobs : ‖recohRationalComplexValue observed - (if positive then truth else -truth)‖ ≤ ε)
    (hcomplete : ε + η ≤ (radius : ℝ))
    (hunique : ε + ((radius : ℝ) + η) < 2) :
    recohRationalSignSame base observed radius = positive := by sorry


variable {G J : Type*} [AddCommGroup G] [DecidableEq G]

local notation "H₂" => recohTorsionSubgroup (G := G) 2





















end Couret.STROBO2TORS
