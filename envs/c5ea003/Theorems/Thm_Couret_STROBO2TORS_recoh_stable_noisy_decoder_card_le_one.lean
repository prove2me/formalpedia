-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_stable_noisy_decoder_card_le_one
-- name    : Couret.STROBO2TORS.recoh_stable_noisy_decoder_card_le_one
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:59:56.556622+00:00
-- url     : https://prove2.me/theorems/c8238617-4618-4042-a631-93029e2735ef
-- title:
--   The guarded stable decoder always returns at most one support
-- statement:
--   Let $G=\prod_{j<d}\mathbb Z/q_j\mathbb Z$ with positive natural moduli $q_j$. Write $P_\chi(A)=\sum_{x\in A}\chi(x)$, $R_A$ for the ordered pair-sum count, and $F(A)$ for its fibre among triples. The stable noisy core generates one recovered candidate per cyclic square representative using binary signs, then filters by rational balls of radius $\tau$ around all predicted stable-bank readings. The guarded decoder first checks the typed square format and valid precision, returning the empty set if either fails. For arbitrary entries $L$, observations $o$, rational $\epsilon$ and natural $m,n$,
--
--   $$|\operatorname{Decoder}(L,o,\epsilon,m,n)|\le1.$$
--
--   Unrealizable squares, failed guards and corrupted readings are included.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohStableReconstruction.lean#L275-L299, lines 275–299; source file SHA-256 6ba847ab84346711528fad14d2971d71a5bd99f9152b733aa4ad067c05fd8df3; theorem Couret.STROBO2TORS.recoh_stable_noisy_decoder_card_le_one

import Aesop
import Definitions.Def_Couret_RecohStableReconstruction_da64f089b51e
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
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
import Mathlib.Topology.Algebra.Order.Floor
import Theorems.Thm_Couret_STROBO2TORS_recoh_noisy_sign_decoder_card_le_representatives
import Theorems.Thm_Couret_STROBO2TORS_recoh_stable_noisy_core_card_le_one
import Definitions.Def_Couret_RecohStableSquareSelection_4ccedec76589
import Definitions.Def_Couret_RecohStableBank_b01db9b053a3
import Definitions.Def_Couret_RecohNoisySignRecovery_25d41afc9bfe
import Definitions.Def_Couret_RecohRationalRoots_2e1442988636

set_option autoImplicit false

/-!
End-to-end stable reconstruction on explicit cyclic products.  The square
determines the bank, rational series determine the prediction centres, and
the decoder generates at most one candidate per square representative.
Precision is supplied by two natural numbers and checked by rational guards.
No complex comparison occurs in the executable definitions.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

theorem recoh_stable_noisy_decoder_card_le_one
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (observed : RecohSelectedBankIndex q entries → RecohRationalComplex)
    (epsilon : ℚ) (machinTerms taylorTerms : ℕ) :
    (recohStableNoisyDecoder q entries observed epsilon machinTerms taylorTerms).card ≤ 1 := by sorry






end Couret.STROBO2TORS
