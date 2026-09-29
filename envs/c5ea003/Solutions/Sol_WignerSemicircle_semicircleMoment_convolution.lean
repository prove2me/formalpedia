-- Prove2me | solution 1 for WignerSemicircle.semicircleMoment_convolution
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:51:58.576643+00:00
-- url     : https://prove2.me/submissions/035a74af-5dbe-4e82-8ce0-af127501f0de

-- Sol generated from Probability/WignerSemicircleRecursion.lean
import Mathlib
import Definitions.Def_Probability_WignerSemicircleMoments
import Theorems.Thm_WignerSemicircle_semicircleMoment_two_mul
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# The semicircle law as the unique fixed point of the moment convolution

The even moments `m_{2k} = ∫ x^{2k} dσ(x)` of the semicircle law satisfy the
*Catalan convolution recursion*

  `m_{2(k+1)} = ∑_{i=0}^{k} m_{2i} · m_{2(k-i)}`,

which is the combinatorial shadow of the Stieltjes fixed-point equation
`m(z) = 1 / (-z - m(z))` for the semicircle transform.  This recursion is exactly
the moment-method identity produced by decomposing a closed `2(k+1)`-walk at the
first return to its starting point.

We prove the recursion, and — more importantly — its converse: the recursion
together with the normalisation `m_0 = 1` **determines** the whole even moment
sequence.  Hence any limiting spectral distribution whose moments obey the
first-return decomposition must be the semicircle law: this is the abstract
uniqueness half of the moment method for Wigner matrices.
-/

open BigOperators Finset

open WignerSemicircle





open WignerSemicircle in
theorem solution(k : ℕ) :
    semicircleMoment (2 * (k + 1))
      = ∑ i ∈ Finset.range (k + 1), semicircleMoment (2 * i) * semicircleMoment (2 * (k - i)) := by
  have hlhs : semicircleMoment (2 * (k + 1)) = (catalan (k + 1) : ℝ) :=
    semicircleMoment_two_mul (k + 1)
  have hrhs : ∀ i ∈ Finset.range (k + 1),
      semicircleMoment (2 * i) * semicircleMoment (2 * (k - i))
        = ((catalan i * catalan (k - i) : ℕ) : ℝ) := by
    intro i _
    rw [semicircleMoment_two_mul i, semicircleMoment_two_mul (k - i)]
    push_cast
    ring
  rw [hlhs, Finset.sum_congr rfl hrhs, ← Nat.cast_sum]
  congr 1
  rw [catalan_succ k, Fin.sum_univ_eq_sum_range (fun i => catalan i * catalan (k - i)) (k + 1)]
