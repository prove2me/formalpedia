-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_ordinary_probe_distance
-- name    : Couret.STROBO2TORS.recoh_ordinary_probe_distance
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:57:07.283698+00:00
-- url     : https://prove2.me/theorems/5f0b73cf-6980-4b4c-996d-ecd1f3963c06
-- title:
--   A separating binary bank detects an ordinary collision quantitatively
-- statement:
--   Let G be an abelian group, S finite supports, chi complex additive characters, P_chi(S)=sum_(x in S)chi(x), and H={u:2u=0}. An H-orbit is {S+u:u in H}. A bank is delta-separated on a finite candidate family if every two distinct candidates have some coordinate whose probe difference has norm at least delta. Let a be any real number, B=(chi_i) any bank, and S,T distinct finite supports with T=S+u for some u in H. Assume every probe on S has norm at least a and the common kernel of B on H is zero. Then $$\exists i,\quad2a\le|P_{\chi_i}(S)-P_{\chi_i}(T)|.$$ No positivity of a or cardinality assumption on supports is imposed.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohProbeStability.lean#L64-L87, lines 64–87; source file SHA-256 1d695a0d84e83ff92491e95ea472df8f9bf1059d52c5525c794d82c7f31a9800; theorem Couret.STROBO2TORS.recoh_ordinary_probe_distance

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_opposite_probe_distance
import Theorems.Thm_Couret_STROBO2TORS_recoh_two_torsion_probe_is_sign
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

theorem recoh_ordinary_probe_distance
    {I : Type*} (bank : I → AddChar G ℂ) (S T : Finset G) (a : ℝ)
    (hamp : ∀ i, a ≤ ‖recohSupportProbe (bank i) S‖)
    (hsep : ∀ u : G, u + u = 0 → (∀ i, bank i u = 1) → u = 0)
    (hordinary : OrdinaryPartner S T) (hST : S ≠ T) :
    ∃ i, 2 * a ≤ ‖recohSupportProbe (bank i) S - recohSupportProbe (bank i) T‖ := by sorry


variable [Fintype G]















end Couret.STROBO2TORS
