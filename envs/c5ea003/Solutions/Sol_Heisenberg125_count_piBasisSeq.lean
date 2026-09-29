-- Prove2me | solution 1 for Heisenberg125.count_piBasisSeq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:45:04.09979+00:00
-- url     : https://prove2.me/submissions/700eb6c9-23fd-4fcb-8f31-425637e6d026

-- Sol generated from Algebra/Heisenberg125/ElementaryAbelian.lean
import Mathlib
import Definitions.Def_Algebra_Heisenberg125_ElementaryAbelian
/-
# Olson's theorem for elementary abelian `p`-groups: `d((Z/p)^k) = k(p-1)`

The conjecture of Godara and Sarkar, `d(H_{p^3}) = 3p - 3`, says that the
non-abelian exponent-`p` group of order `p^3` has the *same* small Davenport
constant as the elementary abelian group `(Z/p)^3` of the same order.  This file
proves the abelian half of that statement in full generality:

  `d((Z/p)^k) = k(p - 1)`  for every prime `p` and every `k`.

* the upper bound is the multi-dimensional Chevalley–Warning bound
  `Heisenberg125.exists_nonempty_zeroSum_sublist_family` of
  `Algebra.Heisenberg125.ZeroSumTwoDim` (`D((Z/p)^k) ≤ k(p-1) + 1`);
* the lower bound is the explicit zero-sum-free sequence
  `e_0^{p-1} e_1^{p-1} ⋯ e_{k-1}^{p-1}`, whose zero-sum-freeness is proved by a
  counting argument: the `j`-th coordinate of the sum of a subsequence is the
  multiplicity of `e_j` in it, and multiplicities are bounded by `p - 1`.

For `k = 3` this gives `d((Z/p)^3) = 3p - 3`, and in particular
`d((Z/5)^3) = 12`, exactly the lower bound proved for `H_125`.
-/

open Heisenberg125

open Multiplicative

variable {p k : ℕ}

/-! ### Two elementary list lemmas -/



/-! ### The standard basis sequence -/



lemma piBasis_ne (hp : 1 < p) {i j : Fin k} (h : i ≠ j) :
    piBasis p k i ≠ piBasis p k j := by
  haveI : Fact (1 < p) := ⟨hp⟩
  intro hc
  have hfun := congrFun (congrArg toAdd hc) i
  simp only [piBasis, toAdd_ofAdd, Pi.single_eq_same, Pi.single_eq_of_ne h] at hfun
  exact one_ne_zero hfun









open Heisenberg125 in
theorem solution(hp : 1 < p) (j : Fin k) :
    (piBasisSeq p k).count (piBasis p k j) = p - 1 := by
  classical
  rw [piBasisSeq, List.count_flatMap]
  have hmap : ((List.finRange k).map
        (List.count (piBasis p k j) ∘ fun i => List.replicate (p - 1) (piBasis p k i)))
      = (List.finRange k).map (fun i => if i = j then p - 1 else 0) := by
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply, List.count_replicate]
    by_cases h : i = j
    · subst h; simp
    · simp [h, piBasis_ne hp h]
  rw [hmap, ← Fin.sum_univ_def]
  simp
