-- Prove2me | Theorems.Thm_BerggrenZeta_treeZeta_summable_iff
-- name    : BerggrenZeta.treeZeta_summable_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-14T01:24:15.618634+00:00
-- url     : https://prove2.me/theorems/3ff92638-f394-4456-b7b0-e55a7e6a15cc
-- title:
--   Main theorem: the abscissa of convergence of the Berggren tree zeta function is `1`.
-- statement:
--   **Main theorem: the abscissa of convergence of the Berggren tree zeta function is `1`.**
--   The series `∑_w c(w)^{-s}` over the nodes of the Berggren tree converges if and only if
--   `s > 1`.
--
--   ```lean
--   theorem BerggrenZeta.treeZeta_summable_iff(s : ℝ) :
--       Summable (fun w : List (Fin 3) => (hyp w : ℝ) ^ (-s)) ↔ 1 < s := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/BerggrenTreeZetaAbscissa.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/BerggrenTreeZetaAbscissa.lean#L241

-- Thm stub generated from Novelty/BerggrenTreeZetaAbscissa.lean
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

-- open removed: section is not a namespace

/-! ## Part A. The tree zeta function as a Dirichlet series over Euclid seeds -/







/-! ## Part B. Convergence for `s > 1` -/



/-! ## Part C. Divergence for `s ≤ 1`: an arithmetic family of seeds -/




/-! ## Part D. The abscissa of convergence is exactly `1` -/

theorem BerggrenZeta.treeZeta_summable_iff(s : ℝ) :
    Summable (fun w : List (Fin 3) => (hyp w : ℝ) ^ (-s)) ↔ 1 < s := by sorry
