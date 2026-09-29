-- Prove2me | solution 1 for BerggrenZeta.not_summable_seedTerm_of_le_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-14T01:42:59.01098+00:00
-- url     : https://prove2.me/submissions/72f75ef1-e3e9-4172-9918-989f3901fdbe

-- Sol generated from Novelty/BerggrenTreeZetaAbscissa.lean
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeZetaAbscissa
import Definitions.Def_Novelty_BerggrenTreeZetaCore
import Theorems.Thm_BerggrenZeta_fibre_lower_bound

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



theorem seedTerm_nonneg (s : ℝ) (p : ℕ × ℕ) : 0 ≤ seedTerm s p :=
  Set.indicator_nonneg (fun _ _ => by positivity) p




/-! ## Part B. Convergence for `s > 1` -/



/-! ## Part C. Divergence for `s ≤ 1`: an arithmetic family of seeds -/




/-! ## Part D. The abscissa of convergence is exactly `1` -/




open BerggrenZeta in
theorem solution{s : ℝ} (hs : s ≤ 1) : ¬ Summable (seedTerm s) := by
  intro hsum
  obtain ⟨hfib0, hfib⟩ := (summable_prod_of_nonneg (seedTerm_nonneg s)).mp hsum
  have hinj : Function.Injective (fun q : Nat.Primes => 2 * (q : ℕ)) := by
    intro a b hab
    simp only at hab
    exact Subtype.ext (by omega)
  have hcomp : Summable (fun q : Nat.Primes => ∑' n : ℕ, seedTerm s (2 * (q : ℕ), n)) :=
    hfib.comp_injective hinj
  have hbig : Summable (fun q : Nat.Primes => 1 / (20 * (q : ℕ) : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun q => by positivity) (fun q => ?_) hcomp
    exact fibre_lower_bound hs q.2 (hfib0 (2 * (q : ℕ)))
  have hharm : Summable (fun q : Nat.Primes => ((q : ℕ) : ℝ) ^ (-(1 : ℝ))) := by
    have := hbig.mul_left 20
    refine this.congr (fun q => ?_)
    have hq0 : (0 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast q.2.pos
    rw [Real.rpow_neg_one]
    field_simp
  exact absurd (Nat.Primes.summable_rpow.mp hharm) (by norm_num)
