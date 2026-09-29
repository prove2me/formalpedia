-- Prove2me | solution 1 for BatchYield.exists_square_subproduct
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:48:51.980676+00:00
-- url     : https://prove2.me/submissions/3ce5bcad-24fe-4582-9d7a-fd7ff006a803

-- Sol generated from Applications/BatchSmoothnessYield.lean
import Mathlib
import Definitions.Def_Applications_BatchSmoothnessCorrectness
import Definitions.Def_Applications_BatchSmoothnessYield
import Theorems.Thm_BatchYield_exists_nonempty_subset_sum_eq_zero

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

/-- A nonzero natural number all of whose prime exponents are even is a square. -/
theorem isSquare_of_even_factorization {n : ℕ} (hn : n ≠ 0)
    (h : ∀ p, Even (n.factorization p)) : IsSquare n := by
  refine ⟨n.factorization.prod (fun p e => p ^ (e / 2)), ?_⟩
  conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  rw [← Finsupp.prod_mul]
  apply Finsupp.prod_congr
  intro p _
  rw [← pow_add]
  congr 1
  obtain ⟨k, hk⟩ := h p
  omega

/-! ## The relation quota of the sieve -/



/-! ## Optimal batch size: one formula for both regimes -/








open BatchYield in
theorem solution{B : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ι → ℕ) (hpos : ∀ i, 0 < n i) (hsmooth : ∀ i, IsSmooth B (n i))
    (h : (Nat.primesBelow (B + 1)).card < Fintype.card ι) :
    ∃ S : Finset ι, S.Nonempty ∧ IsSquare (∏ i ∈ S, n i) := by
  classical
  set κ := {p // p ∈ Nat.primesBelow (B + 1)}
  have hκ : Fintype.card κ = (Nat.primesBelow (B + 1)).card := Fintype.card_coe _
  obtain ⟨S, hSne, hSsum⟩ :=
    exists_nonempty_subset_sum_eq_zero (ι := ι) (κ := κ)
      (fun i => fun p => ((n i).factorization p.1 : ZMod 2)) (by rw [hκ]; exact h)
  refine ⟨S, hSne, ?_⟩
  have hprodpos : (∏ i ∈ S, n i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => (hpos i).ne'
  refine isSquare_of_even_factorization hprodpos ?_
  intro p
  have hfac : (∏ i ∈ S, n i).factorization p = ∑ i ∈ S, (n i).factorization p := by
    rw [Nat.factorization_prod (fun i _ => (hpos i).ne')]
    simp
  rw [hfac]
  by_cases hp : p.Prime
  · by_cases hpB : p ≤ B
    · have hmem : p ∈ Nat.primesBelow (B + 1) := Nat.mem_primesBelow.mpr ⟨by omega, hp⟩
      have := congrFun hSsum ⟨p, hmem⟩
      simp only [Finset.sum_apply, Pi.zero_apply] at this
      rw [← Nat.cast_sum] at this
      exact (ZMod.natCast_eq_zero_iff_even).mp this
    · have : ∀ i ∈ S, (n i).factorization p = 0 := by
        intro i _
        apply Nat.factorization_eq_zero_of_not_dvd
        intro hdvd
        exact hpB (hsmooth i p hp hdvd)
      rw [Finset.sum_congr rfl this]
      simp
  · have : ∀ i ∈ S, (n i).factorization p = 0 := by
      intro i _
      exact Nat.factorization_eq_zero_of_not_prime _ hp
    rw [Finset.sum_congr rfl this]
    simp
