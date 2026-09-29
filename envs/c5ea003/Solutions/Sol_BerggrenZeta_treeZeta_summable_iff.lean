-- Prove2me | solution 1 for BerggrenZeta.treeZeta_summable_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-14T01:46:13.977554+00:00
-- url     : https://prove2.me/submissions/67064adc-766d-4001-81b0-ed1e66befa8b

-- Sol generated from Novelty/BerggrenTreeZetaAbscissa.lean
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeZetaAbscissa
import Definitions.Def_Novelty_BerggrenTreeZetaCore
import Theorems.Thm_BerggrenZeta_not_summable_seedTerm_of_le_one
import Theorems.Thm_BerggrenZeta_summable_seedTerm_of_one_lt

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






/-- The tree series and the seed series are the same series, re-indexed along the
bijection `seedEquiv` between Berggren words and Euclid seeds. -/
theorem summable_tree_iff_seedTerm (s : ℝ) :
    Summable (fun w : List (Fin 3) => (hyp w : ℝ) ^ (-s)) ↔ Summable (seedTerm s) := by
  rw [seedTerm, ← summable_subtype_iff_indicator]
  exact Equiv.summable_iff (f := (fun p : ℕ × ℕ => ((p.1 ^ 2 + p.2 ^ 2 : ℕ) : ℝ) ^ (-s)) ∘
    (Subtype.val : {p : ℕ × ℕ // IsSeed p} → ℕ × ℕ)) seedEquiv

/-! ## Part B. Convergence for `s > 1` -/



/-! ## Part C. Divergence for `s ≤ 1`: an arithmetic family of seeds -/




/-! ## Part D. The abscissa of convergence is exactly `1` -/




open BerggrenZeta in
theorem solution(s : ℝ) :
    Summable (fun w : List (Fin 3) => (hyp w : ℝ) ^ (-s)) ↔ 1 < s := by
  rw [summable_tree_iff_seedTerm]
  constructor
  · intro h
    by_contra hcon
    exact not_summable_seedTerm_of_le_one (not_lt.mp hcon) h
  · exact summable_seedTerm_of_one_lt
