-- Prove2me | solution 1 for BatchYield.exists_nonempty_subset_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:45:48.242201+00:00
-- url     : https://prove2.me/submissions/9ce7e6ee-c510-4c09-87b3-ef9d20daf339

-- Sol generated from Applications/BatchSmoothnessYield.lean
import Mathlib
import Definitions.Def_Applications_BatchSmoothnessCorrectness
import Definitions.Def_Applications_BatchSmoothnessYield

/-!
# Optimal batch size, and the relation quota that batching feeds

Second research cycle on exp 561.  The first cycle established that the
product-tree criterion is *exact*
(`Catalog/Applications/BatchSmoothnessCorrectness.lean`) and that its cost
profile has two opposite regimes
(`Catalog/Applications/BatchSmoothnessCost.lean`): unbounded amortization in the
flat op model, quadratic blow-up in the word model.  Two questions were left
open, and both are answered here.

**Q1 (unification).**  Is the flat/word split really two phenomena, or one?
`blockCost_ge_opt` shows it is one: for a stream of candidates cut into blocks
of size `k`, the per-candidate cost is `A/k + c + q(k-1)`, where `A` is the
per-batch setup, `c` the per-candidate cost and `q` the *quadratic* big-integer
coefficient.  For `q = 0` (flat model) this is strictly decreasing — batch keeps
winning, exactly as measured up to `k = 512`.  For `q > 0` (word model) it has a
unique interior minimum at `k* = √(A/q)`, with optimal value
`c - q + 2√(Aq)` (`blockCost_eq_opt_iff`).  The measured crossover `M* ≈ 1715`
is a shadow of this square root, not of the tree depth.

**Q2 (what the smooth pool is for).**  Exp 561 reports `qs_splits_total = 0` at
bit length 40 / factor base 100: yield below quota.  `exists_square_subproduct`
makes the quota exact — as soon as the batch produces more `B`-smooth relations
than there are primes `≤ B`, a nonempty sub-product is automatically a perfect
square.  The proof is a pigeonhole over `𝔽₂`-exponent vectors
(`exists_nonempty_subset_sum_eq_zero`), bridging linear algebra over `ZMod 2`
with the multiplicative structure of `ℕ`.

## Main results

* `exists_nonempty_subset_sum_eq_zero` — over `ZMod 2`, more vectors than
  coordinates forces a nonempty subset summing to zero (subset-pigeonhole; no
  distinctness hypothesis, so repeated relations are allowed).
* `isSquare_of_even_factorization` — even exponents everywhere means square.
* `exists_square_subproduct` — **relation quota**: `π(B) + 1` smooth relations
  always contain a nonempty sub-family whose product is a perfect square.
* `blockCost_ge_opt`, `blockCost_eq_opt_iff` — the optimal batch size is
  `√(A/q)`, sharp.
* `blockCost_strictAnti_of_flat` — with `q = 0` there is no optimum: the flat
  model's monotone win, recovered as the degenerate case.
-/

open BatchYield

open Finset BatchSmoothness

/-! ## Pigeonhole over `𝔽₂` -/


/-! ## Even exponents give squares -/


/-! ## The relation quota of the sieve -/



/-! ## Optimal batch size: one formula for both regimes -/








open BatchYield in
theorem solution{ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (v : ι → (κ → ZMod 2))
    (h : Fintype.card κ < Fintype.card ι) :
    ∃ S : Finset ι, S.Nonempty ∧ ∑ i ∈ S, v i = 0 := by
  classical
  have hcard : Fintype.card (κ → ZMod 2) < Fintype.card (Finset ι) := by
    rw [Fintype.card_finset, Fintype.card_fun, ZMod.card]
    exact Nat.pow_lt_pow_right (by norm_num) h
  obtain ⟨S, T, hST, hsum⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun S : Finset ι => ∑ i ∈ S, v i) hcard
  refine ⟨(S \ T) ∪ (T \ S), ?_, ?_⟩
  · by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty, Finset.union_eq_empty] at hcon
    obtain ⟨h1, h2⟩ := hcon
    exact hST (Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp h1)
      (Finset.sdiff_eq_empty_iff_subset.mp h2))
  · have hdisj : Disjoint (S \ T) (T \ S) := disjoint_sdiff_sdiff
    have hS : ∑ i ∈ S ∩ T, v i + ∑ i ∈ S \ T, v i = ∑ i ∈ S, v i :=
      Finset.sum_inter_add_sum_diff S T v
    have hT : ∑ i ∈ T ∩ S, v i + ∑ i ∈ T \ S, v i = ∑ i ∈ T, v i :=
      Finset.sum_inter_add_sum_diff T S v
    rw [Finset.inter_comm T S] at hT
    have hab : ∑ i ∈ S \ T, v i = ∑ i ∈ T \ S, v i := by
      have := hS.trans (hsum.trans hT.symm)
      exact add_left_cancel this
    rw [Finset.sum_union hdisj, ← hab]
    funext p
    simp [CharTwo.add_self_eq_zero]
