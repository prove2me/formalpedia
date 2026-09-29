-- Prove2me | solution 1 for BerggrenZeta.treeZeta_abscissa_ne_silver
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-14T01:47:57.23016+00:00
-- url     : https://prove2.me/submissions/a338fee1-3c9f-4cd9-a815-d6ba9112c293

-- Sol generated from Novelty/BerggrenTreeZetaAbscissa.lean
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeZetaAbscissa
import Definitions.Def_Novelty_BerggrenTreeZetaCore
import Theorems.Thm_BerggrenZeta_treeZeta_summable_iff

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
theorem solution:
    ¬ Summable (fun w : List (Fin 3) => (hyp w : ℝ) ^ (-Real.log (1 + Real.sqrt 2))) ∧
    ¬ Summable (fun w : List (Fin 3) =>
        (hyp w : ℝ) ^ (-(Real.log 3 / (2 * Real.log (1 + Real.sqrt 2))))) := by
  have hs2 : Real.sqrt 2 < 3 / 2 := by
    have h : Real.sqrt 2 < Real.sqrt (9 / 4) := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    have : Real.sqrt (9 / 4) = 3 / 2 := by
      rw [show (9 : ℝ) / 4 = (3 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith [h, this.le, this.ge]
  have hs2' : (1 : ℝ) < Real.sqrt 2 := by
    have : Real.sqrt 1 < Real.sqrt 2 := by
      apply Real.sqrt_lt_sqrt <;> norm_num
    simpa using this
  have hlog : Real.log (1 + Real.sqrt 2) < 1 := by
    have h1 : (1 : ℝ) + Real.sqrt 2 < Real.exp 1 := by
      have : Real.exp 1 > 2.7 := by
        have := Real.exp_one_gt_d9
        linarith
      linarith
    calc Real.log (1 + Real.sqrt 2) < Real.log (Real.exp 1) :=
          Real.log_lt_log (by linarith) h1
      _ = 1 := Real.log_exp 1
  have hlogpos : 0 < Real.log (1 + Real.sqrt 2) := Real.log_pos (by linarith)
  constructor
  · rw [treeZeta_summable_iff]
    exact not_lt.mpr hlog.le
  · rw [treeZeta_summable_iff]
    refine not_lt.mpr ?_
    rw [div_le_one (by linarith)]
    have hbig : Real.log 3 ≤ 2 * Real.log (1 + Real.sqrt 2) := by
      have hpow : (1 + Real.sqrt 2) ^ 2 = 3 + 2 * Real.sqrt 2 := by
        have : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        nlinarith [this]
      have h1 : Real.log 3 ≤ Real.log ((1 + Real.sqrt 2) ^ 2) := by
        apply Real.log_le_log (by norm_num)
        rw [hpow]
        linarith
      rwa [Real.log_pow, show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num] at h1
    linarith
