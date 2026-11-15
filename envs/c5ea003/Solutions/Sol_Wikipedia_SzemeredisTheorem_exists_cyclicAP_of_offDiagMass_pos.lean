-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.exists_cyclicAP_of_offDiagMass_pos
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:14:31.84661+00:00
-- url     : https://prove2.me/submissions/83f496cd-8943-4694-84ab-cbe526f6847c

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_CountExtraction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_cyclicAPProduct_pos_iff_of_nonneg

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Weighted arithmetic-progression counts

The transference argument is most naturally stated as a lower bound for a
normalized weighted count of progressions in `ZMod N`.  This file defines
that count and proves its elementary positivity and monotonicity properties.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators







theorem cyclicAPProduct_nonneg {k N : ℕ} {f : ZMod N → ℝ}
    (hf : ∀ x, 0 ≤ f x) (a d : ZMod N) :
    0 ≤ cyclicAPProduct k N f a d := by
  exact Finset.prod_nonneg fun j _ => hf (cyclicAPTerm a d j)















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
/-- Positive off-diagonal mass extracts a nonconstant cyclic progression on
which every factor of the nonnegative weight is strictly positive. -/
theorem solution
    {k N : ℕ} [NeZero N] {f : ZMod N → ℝ}
    (hf : ∀ x, 0 ≤ f x)
    (hmass : 0 < cyclicAPOffDiagMass k N f) :
    ∃ a d : ZMod N, d ≠ 0 ∧
      ∀ j : Fin k, 0 < f (cyclicAPTerm a d j) := by
  classical
  rw [cyclicAPOffDiagMass] at hmass
  have houter_nonneg :
      ∀ a ∈ (Finset.univ : Finset (ZMod N)),
        0 ≤
          ∑ d ∈ (Finset.univ.filter fun d : ZMod N => d ≠ 0),
            cyclicAPProduct k N f a d := by
    intro a _
    exact Finset.sum_nonneg fun d _ => cyclicAPProduct_nonneg hf a d
  obtain ⟨a, _, ha⟩ :=
    (Finset.sum_pos_iff_of_nonneg houter_nonneg).mp hmass
  have hinner_nonneg :
      ∀ d ∈ (Finset.univ.filter fun d : ZMod N => d ≠ 0),
        0 ≤ cyclicAPProduct k N f a d := by
    intro d _
    exact cyclicAPProduct_nonneg hf a d
  obtain ⟨d, hdmem, hdpos⟩ :=
    (Finset.sum_pos_iff_of_nonneg hinner_nonneg).mp ha
  refine ⟨a, d, (Finset.mem_filter.mp hdmem).2, ?_⟩
  exact (cyclicAPProduct_pos_iff_of_nonneg hf a d).mp hdpos
