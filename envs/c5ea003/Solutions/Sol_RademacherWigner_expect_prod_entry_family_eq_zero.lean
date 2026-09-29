-- Prove2me | solution 1 for RademacherWigner.expect_prod_entry_family_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:33:07.396041+00:00
-- url     : https://prove2.me/submissions/8f8487f7-0e0f-4bf3-90b3-9312dfa80ada

-- Sol generated from Probability/WignerAllOrderParity.lean
import Mathlib
import Definitions.Def_Probability_WignerAllOrderParity
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerWalkParity
import Theorems.Thm_RademacherWigner_entry_flipEdge
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# All-order walk expansion of the trace, and the exact vanishing of every odd moment

The files `Probability.WignerRademacherEnsemble` and `Probability.WignerWalkParity`
compute the spectral moments of the symmetric Rademacher ensemble at orders `2`, `3`
and `4`, and isolate the sign-flip involution for a walk of fixed length.  This file
removes the length restriction completely:

* `RademacherWigner.trace_pow_succ_sum_walks` expands `tr (M ^ (m+1))` for an
  *arbitrary* matrix as a sum over closed `(m+1)`-walks, encoded as a starting
  vertex `i` together with the remaining vertices `v : Fin m → Fin N`; the `t`-th
  step goes from `(Fin.cons i v) t` to `(Fin.snoc v i) t`.  This is proved by
  induction from the entrywise path expansion `RademacherWigner.pow_apply_sum_walks`.

* The sign-flip calculus is then developed for an arbitrary finite family of steps
  `a b : ι → Fin N` (`edgeMult`, `prod_entry_flipEdge_family`), giving

  - `expect_prod_entry_family_eq_zero_of_card_odd`: **any** odd-size family of steps
    has vanishing ensemble average, and
  - `prod_entry_eq_one_of_even`: a loop-free family all of whose edge multiplicities
    are even has monomial identically `1`,

  hence the exact dichotomy `expect_prod_entry_family`: the ensemble average of a
  walk monomial is `1` if the walk is loop-free with all edge multiplicities even,
  and `0` otherwise.

* Consequently `expect_trace_pow_eq_sum_indicator` reduces the computation of *every*
  moment `E [tr W^m]` to a purely combinatorial count of even closed walks, and
  `expect_trace_pow_odd` proves that **all odd trace moments vanish exactly, at every
  finite dimension `N` and every odd order** — no asymptotics, no error terms.
  Normalising, `expect_normalizedMoment_odd` matches the odd moments of the
  semicircle law (`WignerUniversal`-style statement at all orders, rather than only
  at order `3`).
-/

open Matrix BigOperators Finset

open RademacherWigner

variable {N : ℕ}

/-! ### Walk expansion of powers and traces of an arbitrary matrix -/



/-! ### The sign-flip calculus for an arbitrary finite family of steps -/

variable {ι : Type*} [Fintype ι]


/-- **Sign-flip rule for a family of steps.**  Flipping the Rademacher variable at
the edge `p` multiplies the monomial `∏ entry (a t) (b t)` by `(-1)` once for every
step traversing `p`. -/
theorem prod_entry_flipEdge_family (g : Config N) (a b : ι → Fin N)
    (p : Fin N × Fin N) :
    (∏ t, entry (flipEdge p g) (a t) (b t))
      = (-1) ^ edgeMult a b p * ∏ t, entry g (a t) (b t) := by
  have h : ∀ t : ι, entry (flipEdge p g) (a t) (b t)
      = (if edgeOf (a t) (b t) = p then (-1 : ℝ) else 1) * entry g (a t) (b t) := by
    intro t
    rw [entry_flipEdge]
    split <;> ring
  rw [Finset.prod_congr rfl fun t _ => h t, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, edgeMult]







/-! ### Consequences for the spectral moments -/







open RademacherWigner in
theorem solution(a b : ι → Fin N) (p : Fin N × Fin N)
    (hodd : Odd (edgeMult a b p)) :
    expect (fun g : Config N => ∏ t, entry g (a t) (b t)) = 0 := by
  have hneg : ∀ g : Config N,
      (∏ t, entry (flipEdge p g) (a t) (b t)) = -∏ t, entry g (a t) (b t) := by
    intro g
    rw [prod_entry_flipEdge_family, hodd.neg_one_pow, neg_one_mul]
  have hsum : (∑ g : Config N, ∏ t, entry g (a t) (b t)) = 0 := by
    have h1 := Equiv.sum_comp (flipEdge (N := N) p)
      (fun g => ∏ t, entry g (a t) (b t))
    rw [Finset.sum_congr rfl fun g _ => hneg g, Finset.sum_neg_distrib] at h1
    linarith
  unfold RademacherWigner.expect
  rw [hsum, zero_div]
