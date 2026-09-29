-- Prove2me | solution 1 for RademacherWigner.expect_prod_entry_family
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:34:57.363501+00:00
-- url     : https://prove2.me/submissions/6594ed79-b776-42d1-94ef-d9d6c8180144

-- Sol generated from Probability/WignerAllOrderParity.lean
import Mathlib
import Definitions.Def_Probability_WignerAllOrderParity
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerWalkParity
import Theorems.Thm_RademacherWigner_expect_const
import Theorems.Thm_RademacherWigner_expect_prod_entry_family_eq_zero
import Theorems.Thm_RademacherWigner_expect_zero
import Theorems.Thm_RademacherWigner_prod_entry_eq_one_of_even
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









/-! ### Consequences for the spectral moments -/







open RademacherWigner in
theorem solution(a b : ι → Fin N) :
    expect (fun g : Config N => ∏ t, entry g (a t) (b t))
      = if (∀ t, a t ≠ b t) ∧ (∀ p, Even (edgeMult a b p)) then 1 else 0 := by
  by_cases hgood : (∀ t, a t ≠ b t) ∧ (∀ p, Even (edgeMult a b p))
  · rw [if_pos hgood]
    have h1 : ∀ g : Config N, (∏ t, entry g (a t) (b t)) = 1 :=
      fun g => prod_entry_eq_one_of_even g a b hgood.1 hgood.2
    simp only [h1]
    exact expect_const 1
  · rw [if_neg hgood]
    by_cases hloop : ∀ t, a t ≠ b t
    · have hodd : ∃ p, Odd (edgeMult a b p) := by
        by_contra hcon
        push_neg at hcon
        refine hgood ⟨hloop, fun p => ?_⟩
        rcases Nat.even_or_odd (edgeMult a b p) with h' | h'
        · exact h'
        · exact absurd h' (hcon p)
      obtain ⟨p, hp⟩ := hodd
      exact expect_prod_entry_family_eq_zero a b p hp
    · push_neg at hloop
      obtain ⟨t, ht⟩ := hloop
      have h0 : ∀ g : Config N, (∏ s, entry g (a s) (b s)) = 0 := by
        intro g
        refine Finset.prod_eq_zero (Finset.mem_univ t) ?_
        rw [entry, if_pos ht]
      simp only [h0]
      exact expect_zero
