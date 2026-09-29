-- Prove2me | solution 1 for BerggrenZeta.summable_boxTerm
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-14T01:43:00.915489+00:00
-- url     : https://prove2.me/submissions/e0421df3-2f14-43a0-98a0-1a52dceb307d

-- Sol generated from Novelty/BerggrenTreeZetaAbscissa.lean
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeZetaAbscissa
import Definitions.Def_Novelty_BerggrenTreeZetaCore

/-!
# The Berggren tree zeta function and its abscissa of convergence

The **tree zeta function** of the Berggren tree of primitive Pythagorean triples is the
Dirichlet series over the nodes of the tree, weighted by the hypotenuse:

`Z_tree(s) = ∑_{w ∈ {L,M,R}*} c(w)^{-s}`.

The moonshot conjecture attached to this project predicted that the abscissa of
convergence of `Z_tree` is governed by the **silver ratio** `1 + √2` — the eigenvalue
structure `3 ± 2√2` of the Berggren generators — for instance
`σ = log 3 / (2 log (1+√2)) ≈ 0.6232` (the "branching over silver growth" exponent), or
`log (1+√2) ≈ 0.8814`.

**This file refutes that prediction and computes the true answer: the abscissa is `1`.**

The mechanism is the growth dichotomy inside the tree: the middle (Pell) branch grows at
the silver rate `(1+√2)^{2k}`, but the two outer branches grow only *quadratically* in the
depth, so the tree contains far more small hypotenuses than a purely exponential branching
model predicts.  In fact — by the bijection `seedEquiv` of the core file — the nodes are in
bijection with Euclid seeds, so `Z_tree` is exactly the Dirichlet series of the primitive
Pythagorean hypotenuses counted with multiplicity, whose counting function is `Θ(H)`, and
the abscissa is `1`.

## Main results

* `summable_seedTerm_of_one_lt` — convergence for `s > 1` (an elementary two-dimensional
  comparison: at most `m` seeds have first coordinate `m`, and each contributes at most
  `m^{-2s}`);
* `not_summable_seedTerm_of_le_one` — divergence for every `s ≤ 1`.  The witness family is
  arithmetic: for each prime `q`, the seeds `(2q, n)` with `n` odd and `n < q` are
  admissible, contribute `≳ 1/(20 q)` in total, and `∑_q 1/q` diverges (Euler).
* `treeZeta_summable_iff` — **the abscissa of convergence of the tree zeta function is
  exactly `1`**;
* `treeZeta_abscissa_ne_silver` — the quantitative refutation: the abscissa is neither
  `log (1+√2)` nor `log 3 / (2 log (1+√2))`.
-/

open BerggrenZeta

open Real

/-! ## Part A. The tree zeta function as a Dirichlet series over Euclid seeds -/







/-! ## Part B. Convergence for `s > 1` -/



/-! ## Part C. Divergence for `s ≤ 1`: an arithmetic family of seeds -/




/-! ## Part D. The abscissa of convergence is exactly `1` -/




open BerggrenZeta in
theorem solution{s : ℝ} (hs : 1 < s) :
    Summable (fun p : ℕ × ℕ => if p.2 < p.1 then (p.1 : ℝ) ^ (-(2 * s)) else 0) := by
  have hnn : (0 : ℕ × ℕ → ℝ) ≤ fun p : ℕ × ℕ => if p.2 < p.1 then (p.1 : ℝ) ^ (-(2 * s)) else 0 := by
    intro p
    dsimp only
    split
    · positivity
    · exact le_rfl
  rw [summable_prod_of_nonneg hnn]
  constructor
  · intro m
    refine summable_of_ne_finset_zero (s := Finset.range m) ?_
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    simp [Nat.not_lt.mpr hn]
  · have hval : ∀ m : ℕ,
        (∑' n : ℕ, if (m, n).2 < (m, n).1 then ((m, n).1 : ℝ) ^ (-(2 * s)) else 0)
          = (m : ℝ) ^ (1 - 2 * s) := by
      intro m
      have hz : ∀ n ∉ Finset.range m,
          (if (m, n).2 < (m, n).1 then ((m, n).1 : ℝ) ^ (-(2 * s)) else 0) = 0 := by
        intro n hn
        simp only [Finset.mem_range, not_lt] at hn
        simp [Nat.not_lt.mpr hn]
      rw [tsum_eq_sum hz]
      have : ∀ n ∈ Finset.range m,
          (if (m, n).2 < (m, n).1 then ((m, n).1 : ℝ) ^ (-(2 * s)) else 0)
            = (m : ℝ) ^ (-(2 * s)) := by
        intro n hn
        simp only [Finset.mem_range] at hn
        simp [hn]
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp
        rw [Real.zero_rpow (by linarith)]
      · have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
        rw [show (1 : ℝ) - 2 * s = 1 + -(2 * s) by ring, Real.rpow_add hm0, Real.rpow_one]
    simp_rw [hval]
    exact Real.summable_nat_rpow.mpr (by linarith)
