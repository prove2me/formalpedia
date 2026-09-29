-- Prove2me | solution 1 for BerggrenZeta.fibre_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-14T01:39:03.598836+00:00
-- url     : https://prove2.me/submissions/5d1ea72a-e403-47e5-b0e3-90dbf6c5815c

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



theorem seedTerm_nonneg (s : ℝ) (p : ℕ × ℕ) : 0 ≤ seedTerm s p :=
  Set.indicator_nonneg (fun _ _ => by positivity) p

theorem seedTerm_of_isSeed {s : ℝ} {p : ℕ × ℕ} (hp : IsSeed p) :
    seedTerm s p = ((p.1 ^ 2 + p.2 ^ 2 : ℕ) : ℝ) ^ (-s) :=
  Set.indicator_of_mem (show p ∈ {p : ℕ × ℕ | IsSeed p} from hp) _



/-! ## Part B. Convergence for `s > 1` -/



/-! ## Part C. Divergence for `s ≤ 1`: an arithmetic family of seeds -/

/-- For a prime `q` and odd `n < q`, the pair `(2q, n)` is an admissible Euclid seed. -/
theorem isSeed_two_mul_prime {q n : ℕ} (hq : q.Prime) (hn : n % 2 = 1) (hnq : n < q) :
    IsSeed (2 * q, n) := by
  have hq2 : 2 ≤ q := hq.two_le
  refine ⟨by simp; omega, by simp; omega, ?_, by simp; omega⟩
  have hcop2 : Nat.Coprime 2 n :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
  have hcopq : Nat.Coprime q n := by
    rw [Nat.Prime.coprime_iff_not_dvd hq]
    intro hdvd
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  exact Nat.Coprime.mul_left hcop2 hcopq



/-! ## Part D. The abscissa of convergence is exactly `1` -/




open BerggrenZeta in
theorem solution{s : ℝ} (hs : s ≤ 1) {q : ℕ} (hq : q.Prime)
    (hfib : Summable (fun n : ℕ => seedTerm s (2 * q, n))) :
    1 / (20 * (q : ℝ)) ≤ ∑' n : ℕ, seedTerm s (2 * q, n) := by
  have hq2 : 2 ≤ q := hq.two_le
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  set F : Finset ℕ := (Finset.range (q / 2)).image (fun j => 2 * j + 1) with hF
  have hinj : Function.Injective (fun j : ℕ => 2 * j + 1) := by
    intro a b hab
    simp only at hab
    omega
  have hcard : F.card = q / 2 := by
    rw [hF, Finset.card_image_of_injective _ hinj, Finset.card_range]
  -- each term of the family is at least `1/(5q²)`
  have hterm : ∀ n ∈ F, 1 / (5 * (q : ℝ) ^ 2) ≤ seedTerm s (2 * q, n) := by
    intro n hn
    rw [hF, Finset.mem_image] at hn
    obtain ⟨j, hj, rfl⟩ := hn
    simp only [Finset.mem_range] at hj
    have hnq : 2 * j + 1 < q := by omega
    have hseed : IsSeed (2 * q, 2 * j + 1) := isSeed_two_mul_prime hq (by omega) hnq
    rw [seedTerm_of_isSeed hseed]
    simp only
    set N : ℕ := (2 * q) ^ 2 + (2 * j + 1) ^ 2 with hN
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
      have : 1 ≤ N := by
        have : 0 < (2 * q) ^ 2 := by positivity
        omega
      exact_mod_cast this
    have hNle : (N : ℝ) ≤ 5 * (q : ℝ) ^ 2 := by
      have hnat : N ≤ 5 * q ^ 2 := by
        have h1 : (2 * j + 1) ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left (by omega) 2
        have h2 : (2 * q) ^ 2 = 4 * q ^ 2 := by ring
        omega
      exact_mod_cast hnat
    calc 1 / (5 * (q : ℝ) ^ 2) ≤ 1 / (N : ℝ) := by
          apply one_div_le_one_div_of_le
          · linarith
          · exact hNle
      _ = (N : ℝ) ^ (-(1 : ℝ)) := by
          rw [Real.rpow_neg_one]
          simp
      _ ≤ (N : ℝ) ^ (-s) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hsum : (F.card : ℝ) * (1 / (5 * (q : ℝ) ^ 2)) ≤ ∑ n ∈ F, seedTerm s (2 * q, n) := by
    have := Finset.card_nsmul_le_sum F _ _ hterm
    simpa [nsmul_eq_mul] using this
  have hle : ∑ n ∈ F, seedTerm s (2 * q, n) ≤ ∑' n : ℕ, seedTerm s (2 * q, n) :=
    hfib.sum_le_tsum F (fun i _ => seedTerm_nonneg s _)
  have hqhalf : (q : ℝ) ≤ 4 * ((q / 2 : ℕ) : ℝ) := by
    have : q ≤ 4 * (q / 2) := by omega
    exact_mod_cast this
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hfinal : 1 / (20 * (q : ℝ)) ≤ (F.card : ℝ) * (1 / (5 * (q : ℝ) ^ 2)) := by
    rw [hcard]
    have h1 : (q : ℝ) / 4 ≤ ((q / 2 : ℕ) : ℝ) := by linarith
    have h2 : 1 / (20 * (q : ℝ)) = ((q : ℝ) / 4) * (1 / (5 * (q : ℝ) ^ 2)) := by
      field_simp
      ring
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  linarith
