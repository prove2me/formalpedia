-- Prove2me | solution 1 for RademacherWigner.pow_apply_sum_walks
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:34:58.409074+00:00
-- url     : https://prove2.me/submissions/fd6597bb-0e23-44be-8ade-13e66b63450c

-- Sol generated from Probability/WignerAllOrderParity.lean
import Mathlib
import Definitions.Def_Probability_WignerAllOrderParity
import Definitions.Def_Probability_WignerWalkParity
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
theorem solution(M : Matrix (Fin N) (Fin N) ℝ) :
    ∀ (m : ℕ) (i j : Fin N),
      (M ^ (m + 1)) i j = ∑ v : Fin m → Fin N, ∏ t : Fin (m + 1),
        M ((Fin.cons i v : Fin (m + 1) → Fin N) t)
          ((Fin.snoc v j : Fin (m + 1) → Fin N) t) := by
  intro m
  induction m with
  | zero =>
      intro i j
      rw [Finset.sum_congr rfl (g := fun _ => M i j) ?_]
      · simp
      · intro v _
        rw [Fin.prod_univ_one, show (0 : Fin 1) = Fin.last 0 from rfl, Fin.snoc_last]
        simp
  | succ m ih =>
      intro i j
      rw [pow_succ, Matrix.mul_apply]
      have h1 : ∀ k : Fin N, (M ^ (m + 1)) i k * M k j
          = ∑ v : Fin m → Fin N, (∏ t : Fin (m + 1),
              M ((Fin.cons i v : Fin (m + 1) → Fin N) t)
                ((Fin.snoc v k : Fin (m + 1) → Fin N) t)) * M k j := by
        intro k; rw [ih i k, Finset.sum_mul]
      rw [Finset.sum_congr rfl fun k _ => h1 k]
      rw [← (Fin.snocEquiv (fun _ : Fin (m + 1) => Fin N)).sum_comp
        (fun u : Fin (m + 1) → Fin N => ∏ t : Fin (m + 2),
          M ((Fin.cons i u : Fin (m + 2) → Fin N) t)
            ((Fin.snoc u j : Fin (m + 2) → Fin N) t))]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun v _ => ?_
      have hu : (Fin.snocEquiv (fun _ : Fin (m + 1) => Fin N)) (k, v)
          = (Fin.snoc v k : Fin (m + 1) → Fin N) := rfl
      rw [hu]
      symm
      rw [Fin.prod_univ_castSucc]
      congr 1
      · refine Finset.prod_congr rfl fun s _ => ?_
        congr 1
        · refine Fin.cases ?_ ?_ s
          · simp
          · intro r
            rw [← Fin.succ_castSucc]
            simp
        · simp
      · congr 1 <;> simp
