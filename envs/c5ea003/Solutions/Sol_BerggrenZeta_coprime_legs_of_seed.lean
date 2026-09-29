-- Prove2me | solution 1 for BerggrenZeta.coprime_legs_of_seed
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-14T01:37:24.700908+00:00
-- url     : https://prove2.me/submissions/1e139094-9205-4cc4-86a1-cfb68d92add3

-- Sol generated from Novelty/BerggrenTreeZetaCore.lean
import Mathlib
import Definitions.Def_Novelty_BerggrenTreeZetaCore

/-!
# The Berggren tree of primitive Pythagorean triples: seeds, words, and the hypotenuse

This file is the combinatorial backbone for the "zeta function of the Berggren tree"
project.  It sets up the Berggren ternary tree in its *Euclid-seed* coordinates and
proves the two facts that make an analytic theory possible at all:

* the map `w ↦ seed w` from ternary words to Euclid seeds is a **bijection** onto the
  set of admissible seeds `S = {(m,n) : n < m, 0 < n, gcd(m,n) = 1, m + n odd}`
  (`seed_bijective_onto_seeds`, `seedEquiv`);
* the hypotenuse of a node is `c(w) = m² + n²` (`hyp`), so the tree zeta function is a
  Dirichlet series over `S`.

The three Berggren matrices act on the seed by
`L (m,n) = (2m - n, m)`, `M (m,n) = (2m + n, m)`, `R (m,n) = (m + 2n, n)`,
and we check (`berggren_matrix_L/M/R`) that on the triple `(m²-n², 2mn, m²+n²)` these are
exactly the classical Berggren matrices
`A₁ = !![1,-2,2; 2,-1,2; 2,-2,3]`, `A₂ = !![1,2,2; 2,1,2; 2,2,3]`,
`A₃ = !![-1,2,2; -2,1,2; -2,2,3]` (the last one is `B₃` of `Shared.BerggrenTrees.B`).

## Main results

* `seed_isSeed` — every node of the tree is an admissible Euclid seed;
* `isSeed_reachable` — **completeness** (Berggren's theorem): every admissible seed is a
  node of the tree;
* `seed_injective` — **uniqueness**: distinct words give distinct nodes;
* `seedEquiv` — the resulting equivalence `List (Fin 3) ≃ {p // IsSeed p}`;
* `node_isPPT` — every node carries a primitive Pythagorean triple;
* `hyp_le_silver_pow`, `Mspine_hyp` , `Rspine_hyp` — the growth dichotomy: the largest
  hypotenuse at depth `k` grows like the square of the silver ratio `(1+√2)² = 3+2√2`,
  while the `R`-spine grows only quadratically (`2k² + 6k + 5`).
-/

open BerggrenZeta

/-! ## Part A. Seeds, moves and the tree -/












/-! ## Part B. The seed condition is preserved by the moves -/









/-! ## Part C. Completeness: every admissible seed occurs in the tree -/







/-! ## Part D. Uniqueness: the word is determined by the node -/













/-! ## Part E. The Pythagorean triple at a node, and the Berggren matrices -/








open BerggrenZeta in
theorem solution{m n : ℕ} (h1 : n < m) (h3 : Nat.Coprime m n)
    (h4 : (m + n) % 2 = 1) : Nat.Coprime (m ^ 2 - n ^ 2) (2 * m * n) := by
  obtain ⟨k, hk⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
  subst hk
  have hfac : (n + k) ^ 2 - n ^ 2 = k * (k + 2 * n) := by
    have : (n + k) ^ 2 = n ^ 2 + k * (k + 2 * n) := by ring
    omega
  have hodd : ((n + k) ^ 2 - n ^ 2) % 2 = 1 := by
    rw [hfac]
    have hk1 : Odd k := Nat.odd_iff.mpr (by omega)
    have hk2 : Odd (k + 2 * n) := Nat.odd_iff.mpr (by omega)
    exact Nat.odd_iff.mp (hk1.mul hk2)
  by_contra hcon
  obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcon
  set m := n + k with hm
  have hp2 : p ≠ 2 := by
    rintro rfl
    omega
  have hpmn : p ∣ m ∨ p ∣ n := by
    have h2mn : p ∣ 2 * (m * n) := by rw [← mul_assoc]; exact hpb
    rcases (Nat.Prime.dvd_mul hp).mp h2mn with h | h
    · exact absurd (Nat.le_of_dvd (by norm_num) h) (by have := hp.two_le; omega)
    · exact (Nat.Prime.dvd_mul hp).mp h
  have hsqle : n ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left (le_of_lt h1) 2
  rcases hpmn with hmm | hn
  · have hm2 : p ∣ m ^ 2 := Dvd.dvd.pow hmm (by norm_num)
    have hn2 : p ∣ n ^ 2 := by
      have hsub := Nat.dvd_sub hm2 hpa
      rwa [show m ^ 2 - (m ^ 2 - n ^ 2) = n ^ 2 by omega] at hsub
    have : p ∣ Nat.gcd m n := Nat.dvd_gcd hmm (hp.dvd_of_dvd_pow hn2)
    rw [h3] at this
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one this)
  · have hn2 : p ∣ n ^ 2 := Dvd.dvd.pow hn (by norm_num)
    have hm2 : p ∣ m ^ 2 := by
      have := dvd_add hpa hn2
      rwa [show m ^ 2 - n ^ 2 + n ^ 2 = m ^ 2 by omega] at this
    have : p ∣ Nat.gcd m n := Nat.dvd_gcd (hp.dvd_of_dvd_pow hm2) hn
    rw [h3] at this
    exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one this)
