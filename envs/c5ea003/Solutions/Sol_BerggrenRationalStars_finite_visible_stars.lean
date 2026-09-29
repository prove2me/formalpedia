-- Prove2me | solution 1 for BerggrenRationalStars.finite_visible_stars
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T03:44:51.83998+00:00
-- url     : https://prove2.me/submissions/72634d37-b592-461f-8942-a7c0dc56231f

-- Sol generated from Cryptography/BerggrenStars/StarHierarchy.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenStars_RationalStars

/-!
# Why the stars sit at rationals, and why only finitely many of them are visible

Two complementary facts finish the explanation of the star map of the Berggren tree.

## Main results

* `no_line_through_irrational` : **there is no star at an irrational boundary point.** If two
  Berggren nodes lie on one Euclidean line through an ideal point `α` with `α` irrational, then
  they are the same node. Radial lines can only emanate from *rational* boundary points; the
  irrational directions of the picture carry no line at all, however dense the nodes are near
  them.
* `finite_visible_stars` : **the visible hierarchy is finite.** For every resolution threshold
  `ε > 0` only finitely many rationals `p/q ∈ [0,1]` have a star of resolution
  `δ(p/q) = starGapNum p q / q ≥ ε`. Combined with `BerggrenRationalStars.visible_rationals`,
  which computes the list for `ε = 2/5`, this says the star map has a discrete, computable
  hierarchy of visible directions rather than a continuum of them.
-/

open BerggrenRationalStars

open BerggrenHypercycleStars




open BerggrenRationalStars in
theorem solution(eps : ℝ) (heps : 0 < eps) :
    {pq : ℕ × ℕ | 0 < pq.2 ∧ pq.1 ≤ pq.2 ∧ eps ≤ (starGapNum pq.1 pq.2 : ℝ) / pq.2}.Finite := by
  obtain ⟨K, hK⟩ := exists_nat_gt (2 / eps)
  have hsub : {pq : ℕ × ℕ | 0 < pq.2 ∧ pq.1 ≤ pq.2 ∧ eps ≤ (starGapNum pq.1 pq.2 : ℝ) / pq.2}
      ⊆ ↑((Finset.range (K + 1)) ×ˢ (Finset.range (K + 1))) := by
    rintro ⟨p, q⟩ ⟨hq, hpq, hge⟩
    have hQ : (0 : ℝ) < q := by exact_mod_cast hq
    have hg2 : (starGapNum p q : ℝ) ≤ 2 := by
      unfold starGapNum
      split_ifs <;> norm_num
    have hqle : (q : ℝ) ≤ 2 / eps := by
      rw [le_div_iff₀ heps]
      have : eps * q ≤ (starGapNum p q : ℝ) := by
        rw [le_div_iff₀ hQ] at hge
        linarith
      linarith
    have hqK : q < K + 1 := by
      have : (q : ℝ) < K := lt_of_le_of_lt hqle hK
      have : q < K := by exact_mod_cast this
      omega
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  exact Set.Finite.subset (Finset.finite_toSet _) hsub
