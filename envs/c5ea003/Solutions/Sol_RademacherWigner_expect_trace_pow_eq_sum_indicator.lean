-- Prove2me | solution 1 for RademacherWigner.expect_trace_pow_eq_sum_indicator
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:41:22.108965+00:00
-- url     : https://prove2.me/submissions/9eb541bf-2b40-4b0d-97e0-94217e18885c

-- Sol generated from Probability/WignerAllOrderParity.lean
import Mathlib
import Definitions.Def_Probability_WignerAllOrderParity
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerWalkParity
import Theorems.Thm_RademacherWigner_expect_prod_entry_family
import Theorems.Thm_RademacherWigner_expect_sum
import Theorems.Thm_RademacherWigner_trace_pow_succ_sum_walks
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
theorem solution(m : ℕ) :
    expect (fun g : Config N => ((W g) ^ (m + 1)).trace)
      = ∑ i : Fin N, ∑ v : Fin m → Fin N, if IsEvenWalk m i v then (1 : ℝ) else 0 := by
  have h1 : ∀ g : Config N, ((W g) ^ (m + 1)).trace
      = ∑ i : Fin N, ∑ v : Fin m → Fin N, ∏ t : Fin (m + 1),
        entry g ((Fin.cons i v : Fin (m + 1) → Fin N) t)
          ((Fin.snoc v i : Fin (m + 1) → Fin N) t) := by
    intro g
    simpa using trace_pow_succ_sum_walks (W g) m
  simp only [h1]
  rw [expect_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [expect_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [expect_prod_entry_family]
  by_cases h : IsEvenWalk m i v
  · rw [if_pos h]
    exact if_pos h
  · rw [if_neg h]
    exact if_neg h
