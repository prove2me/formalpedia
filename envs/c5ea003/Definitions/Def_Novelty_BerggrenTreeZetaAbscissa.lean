-- Prove2me | Definitions.Def_Novelty_BerggrenTreeZetaAbscissa
-- name    : Novelty_BerggrenTreeZetaAbscissa
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-14T01:20:43.289854+00:00
-- url     : https://prove2.me/theorems/4a6f8aa6-ebf4-4d04-ba7d-a392ab3febfb
-- title:
--   Aether Catalog definitions — Novelty_BerggrenTreeZetaAbscissa
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.BerggrenTreeZetaAbscissa`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/BerggrenTreeZetaAbscissa.lean by skeleton subtraction
import Mathlib
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

namespace BerggrenZeta

open Real

/-! ## Part A. The tree zeta function as a Dirichlet series over Euclid seeds -/


/-- The same Dirichlet series written on the set of Euclid seeds, extended by `0`. -/
noncomputable def seedTerm (s : ℝ) : ℕ × ℕ → ℝ :=
  Set.indicator {p : ℕ × ℕ | IsSeed p} (fun p => ((p.1 ^ 2 + p.2 ^ 2 : ℕ) : ℝ) ^ (-s))





/-! ## Part B. Convergence for `s > 1` -/



/-! ## Part C. Divergence for `s ≤ 1`: an arithmetic family of seeds -/




/-! ## Part D. The abscissa of convergence is exactly `1` -/



end BerggrenZeta


