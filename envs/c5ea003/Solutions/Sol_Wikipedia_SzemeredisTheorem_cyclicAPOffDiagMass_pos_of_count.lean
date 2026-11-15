-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.cyclicAPOffDiagMass_pos_of_count
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:14:31.689139+00:00
-- url     : https://prove2.me/submissions/c8a59525-d948-4549-9f30-08f6a1acc49c

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_CountExtraction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_cyclicAPDiagonalMass_le
import Theorems.Thm_Wikipedia_SzemeredisTheorem_cyclicAPMass_eq_diagonal_add_offDiagMass

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

















/-- If the full mass strictly exceeds its diagonal contribution, the
off-diagonal mass is positive. -/
theorem cyclicAPOffDiagMass_pos_of_diagonal_lt_mass
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ)
    (h :
      cyclicAPDiagonalMass k N f <
        cyclicAPMass k N f) :
    0 < cyclicAPOffDiagMass k N f := by
  rw [cyclicAPMass_eq_diagonal_add_offDiagMass] at h
  linarith

/-- The normalized count is the full mass divided once for each cyclic
parameter. -/
theorem cyclicAPCount_eq_mass_div_div
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    cyclicAPCount k N f =
      cyclicAPMass k N f / (N : ℝ) / (N : ℝ) := by
  simp [cyclicAPCount, cyclicAPMass, mean₂, mean,
    Fintype.expect_eq_sum_div_card, ZMod.card, Finset.sum_div]

/-- Clearing the two nonzero normalization factors recovers the full
unnormalized mass. -/
theorem cyclicAPMass_eq_mul_mul_count
    (k N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    cyclicAPMass k N f =
      (N : ℝ) * (N : ℝ) * cyclicAPCount k N f := by
  rw [cyclicAPCount_eq_mass_div_div]
  have hN : (N : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne N)
  field_simp











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
/-- A normalized count which dominates the normalized diagonal-height bound
already forces positive off-diagonal mass. -/
theorem solution
    {k N : ℕ} [NeZero N] {f : ZMod N → ℝ} {B : ℝ}
    (hk : 1 ≤ k)
    (hf0 : ∀ x, 0 ≤ f x)
    (hfB : ∀ x, f x ≤ B)
    (hcount :
      B ^ (k - 1) * mean f <
        (N : ℝ) * cyclicAPCount k N f) :
    0 < cyclicAPOffDiagMass k N f := by
  apply cyclicAPOffDiagMass_pos_of_diagonal_lt_mass
  have hN : 0 < (N : ℝ) := by
    exact_mod_cast NeZero.pos N
  calc
    cyclicAPDiagonalMass k N f ≤
        B ^ (k - 1) * (N : ℝ) * mean f :=
      cyclicAPDiagonalMass_le hk hf0 hfB
    _ = (N : ℝ) * (B ^ (k - 1) * mean f) := by ring
    _ < (N : ℝ) *
        ((N : ℝ) * cyclicAPCount k N f) :=
      mul_lt_mul_of_pos_left hcount hN
    _ = cyclicAPMass k N f := by
      rw [cyclicAPMass_eq_mul_mul_count]
      ring
