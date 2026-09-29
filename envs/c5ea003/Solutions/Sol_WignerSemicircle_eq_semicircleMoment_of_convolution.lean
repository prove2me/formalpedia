-- Prove2me | solution 1 for WignerSemicircle.eq_semicircleMoment_of_convolution
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:53:33.224414+00:00
-- url     : https://prove2.me/submissions/f1e93a3e-9c91-4eff-93b5-e14135fa8fb5

-- Sol generated from Probability/WignerSemicircleRecursion.lean
import Mathlib
import Definitions.Def_Probability_WignerSemicircleMoments
import Theorems.Thm_WignerSemicircle_semicircleMoment_convolution
import Theorems.Thm_WignerSemicircle_semicircleMoment_zero
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
theorem solution(a : ℕ → ℝ) (h0 : a 0 = 1)
    (hrec : ∀ k, a (k + 1) = ∑ i ∈ Finset.range (k + 1), a i * a (k - i)) :
    ∀ k, a k = semicircleMoment (2 * k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simpa [h0] using semicircleMoment_zero.symm
    | (n + 1) =>
        rw [hrec n, semicircleMoment_convolution n]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hin : i < n + 1 := Finset.mem_range.1 hi
        have h1 : a i = semicircleMoment (2 * i) := ih i hin
        have h2 : a (n - i) = semicircleMoment (2 * (n - i)) :=
          ih (n - i) (lt_of_le_of_lt (Nat.sub_le n i) (Nat.lt_succ_self n))
        rw [h1, h2]
