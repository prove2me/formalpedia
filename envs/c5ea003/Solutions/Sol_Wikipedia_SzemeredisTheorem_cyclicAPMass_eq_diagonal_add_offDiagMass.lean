-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.cyclicAPMass_eq_diagonal_add_offDiagMass
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:08:48.430778+00:00
-- url     : https://prove2.me/submissions/4f9f1b68-ff13-4718-8fdc-279ee74641fa

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_CountExtraction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Extracting an off-diagonal cyclic progression

For extraction it is convenient to use unnormalized finite masses.  In
particular, summing over the filtered finset of nonzero differences avoids
introducing a type of nonzero residues, which would be empty when `N = 1`,
and avoids dividing by `N - 1`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators







@[simp]
theorem cyclicAPProduct_zero_difference
    (k N : ℕ) (f : ZMod N → ℝ) (a : ZMod N) :
    cyclicAPProduct k N f a 0 = f a ^ k := by
  simp [cyclicAPProduct, cyclicAPTerm]

























end Wikipedia.SzemeredisTheorem

end
/-!
# Extracting an off-diagonal cyclic progression

For extraction it is convenient to use unnormalized finite masses.  In
particular, summing over the filtered finset of nonzero differences avoids
introducing a type of nonzero residues, which would be empty when `N = 1`,
and avoids dividing by `N - 1`.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

open Wikipedia.SzemeredisTheorem in
/-- The full unnormalized mass splits into its diagonal and off-diagonal
parts. -/
theorem solution
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    cyclicAPMass k N f =
      cyclicAPDiagonalMass k N f + cyclicAPOffDiagMass k N f := by
  classical
  rw [cyclicAPMass, cyclicAPDiagonalMass, cyclicAPOffDiagMass,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  have hdiagonal :
      ∑ d ∈ (Finset.univ.filter fun d : ZMod N => d = 0),
        cyclicAPProduct k N f a d =
          cyclicAPProduct k N f a 0 := by
    apply Finset.sum_eq_single 0
    · intro d hd hd0
      exact (hd0 (Finset.mem_filter.mp hd).2).elim
    · simp
  rw [← Finset.sum_filter_add_sum_filter_not
    (s := Finset.univ) (p := fun d : ZMod N => d = 0)
    (f := fun d => cyclicAPProduct k N f a d)]
  rw [hdiagonal]
