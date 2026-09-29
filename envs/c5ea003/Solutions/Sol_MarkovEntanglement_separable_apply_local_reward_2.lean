-- Prove2me | solution 2 for MarkovEntanglement.separable_apply_local_reward
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-07T15:35:44.558505+00:00
-- url     : https://prove2.me/submissions/4ca28c66-f0ff-4958-9c1a-c0cb78de0f3d

import Definitions.Def_markov_entanglement_multi

open scoped BigOperators
open MarkovEntanglement

/-!
Chen and Peng, *Multi-agent Markov Entanglement*, arXiv:2506.02385v3, Lemma 6, p. 40:
a separable transition applied to a reward that depends on agent `i` alone acts only
through agent `i`'s factor, the other agents' factors being absorbed by `⊗ e`.

Fix a summand `k` of the affine combination.  Its joint transition row at `p` is the
product `∏ j, Pj k j (p j) (q j)`, so the inner sum to evaluate is
`∑ q, (∏ j, Pj k j (p j) (q j)) * r (q i)`.

Absorb the reward into the `i`-th factor: with `f j u = Pj k j (p j) u` and
`g = Function.update f i (fun u => f i u * r u)`, one has
`∏ j, g j (q j) = (∏ j, f j (q j)) * r (q i)` (peel off the `i`-th factor; on
`univ.erase i` the update is invisible).  Summing over the joint space and applying
distributivity over a `Pi` type (`Fintype.prod_sum`) turns the sum of products into a
product of sums,
`∑ q, ∏ j, g j (q j) = ∏ j, ∑ u, g j u`,
whose `j ≠ i` factors are rows of transition matrices and hence equal `1`, leaving exactly
`∑ t, Pj k i (p i) t * r t`.  The hypothesis `hx` on the coefficients is not needed for
this identity — it matters only when Lemma 6 is used to build the value decomposition.
-/

theorem solution
    {N : ℕ} {S : Fin N → Type*} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]
    {K : ℕ} (x : Fin K → ℝ) (Pj : Fin K → ∀ i, Matrix (S i) (S i) ℝ)
    (hPj : ∀ k i, IsTransitionMatrix (Pj k i)) (hx : ∑ k, x k = 1)
    (i : Fin N) (r : S i → ℝ) (p : Joint S) :
    ∑ q : Joint S, (∑ k, x k • tensorProdN (Pj k)) p q * r (q i)
      = ∑ k, x k * ∑ t : S i, Pj k i (p i) t * r t := by
  classical
  -- The single-summand identity: the heart of the lemma.
  have key : ∀ k : Fin K,
      ∑ q : Joint S, (∏ j, Pj k j (p j) (q j)) * r (q i)
        = ∑ t : S i, Pj k i (p i) t * r t := by
    intro k
    set f : ∀ j, S j → ℝ := fun j u => Pj k j (p j) u with hf
    set g : ∀ j, S j → ℝ := Function.update f i (fun u => f i u * r u) with hg
    -- `g` differs from `f` only at `i`, where it carries the reward.
    have hgi : g i = fun u => f i u * r u := by rw [hg, Function.update_self]
    have hgj : ∀ j, j ≠ i → g j = f j := fun j hj => by rw [hg, Function.update_of_ne hj]
    have hprod : ∀ q : Joint S, ∏ j, g j (q j) = (∏ j, f j (q j)) * r (q i) := by
      intro q
      rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin N)) (fun j => g j (q j))
            (Finset.mem_univ i),
          ← Finset.mul_prod_erase (Finset.univ : Finset (Fin N)) (fun j => f j (q j))
            (Finset.mem_univ i)]
      have : ∏ j ∈ Finset.univ.erase i, g j (q j) = ∏ j ∈ Finset.univ.erase i, f j (q j) :=
        Finset.prod_congr rfl fun j hj => by rw [hgj j (Finset.ne_of_mem_erase hj)]
      rw [this, hgi]
      ring
    calc ∑ q : Joint S, (∏ j, f j (q j)) * r (q i)
        = ∑ q : Joint S, ∏ j, g j (q j) := by
          exact (Finset.sum_congr rfl fun q _ => hprod q).symm
      _ = ∏ j, ∑ u : S j, g j u := (Fintype.prod_sum fun j u => g j u).symm
      _ = ∑ t : S i, Pj k i (p i) t * r t := by
          rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin N))
                (fun j => ∑ u : S j, g j u) (Finset.mem_univ i)]
          have hone : ∏ j ∈ Finset.univ.erase i, ∑ u : S j, g j u = 1 := by
            refine Finset.prod_eq_one fun j hj => ?_
            rw [hgj j (Finset.ne_of_mem_erase hj)]
            exact (hPj k j).2 (p j)
          rw [hone, mul_one, hgi]
  -- Expand the affine combination and exchange the two sums.
  have happ : ∀ q : Joint S,
      (∑ k, x k • tensorProdN (Pj k)) p q = ∑ k, x k * ∏ j, Pj k j (p j) (q j) := by
    intro q
    rw [Matrix.sum_apply]
    exact Finset.sum_congr rfl fun k _ => rfl
  calc ∑ q : Joint S, (∑ k, x k • tensorProdN (Pj k)) p q * r (q i)
      = ∑ q : Joint S, ∑ k, x k * ((∏ j, Pj k j (p j) (q j)) * r (q i)) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [happ q, Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ k, x k * ∑ q : Joint S, (∏ j, Pj k j (p j) (q j)) * r (q i) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ k, x k * ∑ t : S i, Pj k i (p i) t * r t :=
        Finset.sum_congr rfl fun k _ => by rw [key k]
