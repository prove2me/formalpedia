-- Prove2me | solution 1 for BerggrenZeta.summable_seedTerm_of_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-14T01:45:05.065082+00:00
-- url     : https://prove2.me/submissions/97ba82c0-a863-4fe3-91a4-79f500b1415a

-- Sol generated from Novelty/BerggrenTreeZetaAbscissa.lean
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeZetaAbscissa
import Definitions.Def_Novelty_BerggrenTreeZetaCore
import Theorems.Thm_BerggrenZeta_summable_boxTerm

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

theorem seedTerm_of_isSeed {s : ℝ} {p : ℕ × ℕ} (hp : IsSeed p) :
    seedTerm s p = ((p.1 ^ 2 + p.2 ^ 2 : ℕ) : ℝ) ^ (-s) :=
  Set.indicator_of_mem (show p ∈ {p : ℕ × ℕ | IsSeed p} from hp) _

theorem seedTerm_of_not_isSeed {s : ℝ} {p : ℕ × ℕ} (hp : ¬ IsSeed p) : seedTerm s p = 0 :=
  Set.indicator_of_notMem (show p ∉ {p : ℕ × ℕ | IsSeed p} from hp) _


/-! ## Part B. Convergence for `s > 1` -/



/-! ## Part C. Divergence for `s ≤ 1`: an arithmetic family of seeds -/




/-! ## Part D. The abscissa of convergence is exactly `1` -/




open BerggrenZeta in
theorem solution{s : ℝ} (hs : 1 < s) : Summable (seedTerm s) := by
  refine Summable.of_nonneg_of_le (seedTerm_nonneg s) ?_ (summable_boxTerm hs)
  intro p
  by_cases hp : IsSeed p
  · rw [seedTerm_of_isSeed hp]
    have hlt : p.2 < p.1 := hp.1
    have hm0 : (0 : ℝ) < (p.1 : ℝ) := by
      have : 0 < p.1 := lt_of_le_of_lt (Nat.zero_le _) hlt
      exact_mod_cast this
    rw [if_pos hlt]
    have hbase : ((p.1 : ℝ) ^ 2) ≤ ((p.1 ^ 2 + p.2 ^ 2 : ℕ) : ℝ) := by
      push_cast
      nlinarith [sq_nonneg ((p.2 : ℝ))]
    have hrw : (p.1 : ℝ) ^ (-(2 * s)) = ((p.1 : ℝ) ^ 2) ^ (-s) := by
      rw [show ((p.1 : ℝ) ^ 2) = (p.1 : ℝ) ^ (2 : ℝ) by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast],
        ← Real.rpow_mul (le_of_lt hm0)]
      ring_nf
    rw [hrw]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)
  · rw [seedTerm_of_not_isSeed hp]
    split
    · positivity
    · exact le_rfl
