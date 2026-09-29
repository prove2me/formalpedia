-- Prove2me | solution 1 for StochasticGalois.card_roots_fiber
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:50:33.22553+00:00
-- url     : https://prove2.me/submissions/1d4cf134-ff03-4344-914e-f7c2adb93146

-- Sol generated from Novelty/StochasticGaloisRoots.lean
import Mathlib
import Definitions.Def_Novelty_StochasticGaloisRoots
/-
# Stochastic Galois Theory over Finite Fields: the Expected-Roots Identity

This file establishes the cleanest instance of the "random polynomial behaves like a
random permutation" correspondence over a finite field (indeed, over any finite
commutative ring).

A monic polynomial of degree `n` over `K` is encoded by its coefficient vector
`v : Fin n → K`, standing for `X^n + ∑ i, v i • X^i`.  Its *roots* in `K` are the
`r : K` with `monicEval n v r = 0`; these correspond exactly to the *linear factors*
of the polynomial, i.e. to the *fixed points* of the associated Frobenius permutation.

The main theorem `total_root_incidences` says that, summed over all `q^n` monic
polynomials of degree `n ≥ 1`, the total number of (polynomial, root) incidences is
exactly `q^n`.  Dividing by the number of polynomials, the **expected number of roots
of a uniformly random monic degree-`n` polynomial is exactly `1`** — matching the
classical fact that a uniformly random permutation in `S_n` has, on average, exactly
one fixed point.  This is the finite-field shadow of the random-permutation model of
Galois groups.
-/

open Finset BigOperators

open StochasticGalois

variable {K : Type*} [CommRing K] [Fintype K] [DecidableEq K]


/-
**Fiber count.** For a fixed base point `r`, the number of monic polynomials of
degree `m + 1` having `r` as a root is `q^m` (where `q = |K|`): the constant coefficient
`v 0` is forced by the remaining coefficients, so the solution set is a graph over
`Fin m → K`.
-/

/-
**Total (polynomial, root) incidences.** For `n ≥ 1`, summing the number of roots
over all `q^n` monic degree-`n` polynomials gives exactly `q^n`.  Equivalently, the
expected number of roots of a uniformly random monic degree-`n` polynomial over a
finite commutative ring is exactly `1`.
-/



open StochasticGalois in
theorem solution(m : ℕ) (r : K) :
    (Finset.univ.filter (fun v : Fin (m + 1) → K => monicEval (m + 1) v r = 0)).card
      = (Fintype.card K) ^ m := by
  by_contra h_contra;
  -- Consider the set of functions $v : Fin (m + 1) → K$ such that $monicEval (m + 1) v r = 0$.
  set S := {v : Fin (m + 1) → K | monicEval (m + 1) v r = 0} with hS_def;
  -- By definition of $S$, we know that for any $v \in S$, $v 0 = -(r^{m+1} + \sum_{j : Fin m} v j.succ * r^{j.succ})$.
  have hS_char : ∀ v : Fin (m + 1) → K, v ∈ S ↔ v 0 = -(r^(m+1) + ∑ j : Fin m, v j.succ * r^(j.succ:ℕ)) := by
    simp +decide [ S, monicEval ];
    intro v; rw [ Fin.sum_univ_succ ] ; simp +decide ; constructor <;> intro h <;> linear_combination' h;
  -- Therefore, the set $S$ is in bijection with the set of functions $w : Fin m → K$.
  have hS_bij : S ≃ (Fin m → K) := by
    refine' Equiv.ofBijective ( fun v => fun j => v.val j.succ ) ⟨ fun a b h => _, fun a => _ ⟩;
    · ext i; induction i using Fin.inductionOn <;> simp_all +decide [ funext_iff ] ;
      rw [ hS_char _ |>.1 a.2, hS_char _ |>.1 b.2 ] ; aesop;
    · refine' ⟨ ⟨ Fin.cons ( - ( r ^ ( m + 1 ) + ∑ j : Fin m, a j * r ^ ( j.succ : ℕ ) ) ) a, _ ⟩, _ ⟩ <;> simp +decide [ hS_char ];
  have := Fintype.card_congr hS_bij; simp_all +decide [ Fintype.card_pi ] ;
  exact h_contra ( by simpa [ Fintype.card_subtype ] using this )
