-- Prove2me | solution 1 for ProofsInTheBook.Chapter29.chapter29
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T16:13:06.82161+00:00
-- url     : https://prove2.me/submissions/b881170d-cd9f-4dac-96a0-97bf63c8ec6e

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter29


/-!
# Chapter 29: Shuffling cards

From "Proofs from THE BOOK":

**Gilbert-Shannon-Reeds riffle shuffles**: the distribution of an `a`-shuffle
on permutations is obtained by uniformly assigning each of the `n` cards one
of `a` labels, then stably sorting by labels.

The book then uses this distribution to analyze total-variation mixing:
about `(3 / 2) * log_2 n` riffle shuffles suffice, and seven shuffles are
enough for a 52-card deck.  This file proves the finite GSR distribution
formula.  The unformalized endpoint is the total-variation statement
`(1 / 2) * sum_sigma |P_{2^k,n}(sigma) - 1 / n!|`, where `P_{a,n}` is the
GSR distribution proved below; the book's cutoff theorem says this drops at
about `k = (3 / 2) * log_2 n`, with the standard 52-card numerical conclusion
at `k = 7`.  That analytic estimate remains an honest frontier: it requires
the Bayer-Diaconis closed formula and real asymptotic/numerical estimates not
developed here.
-/

namespace ProofsInTheBook.Chapter29

/-!
### Riffle-label counting

In the Gilbert-Shannon-Reeds model, an `a`-shuffle can be encoded by assigning
each of the `n` cards one of `a` pile labels, then preserving relative order
inside each pile.  This file records the basic count of such labelings.
-/





































































private theorem exists_adjacent_drop_nat {α : Type*} [LinearOrder α] (f : ℕ → α) :
    ∀ {i j : ℕ}, i < j → f j < f i →
      ∃ k : ℕ, i ≤ k ∧ k + 1 ≤ j ∧ f (k + 1) < f k := by
  intro i j hij hdrop
  induction j generalizing i with
  | zero =>
      exact (Nat.not_lt_zero _ hij).elim
  | succ j ih =>
      by_cases hij' : i < j
      · by_cases hstep : f (j + 1) < f j
        · exact ⟨j, Nat.le_of_lt hij', le_rfl, hstep⟩
        · have hle : f j ≤ f (j + 1) := le_of_not_gt hstep
          have hdrop' : f j < f i := lt_of_le_of_lt hle hdrop
          rcases ih hij' hdrop' with ⟨k, hik, hkj, hkdrop⟩
          exact ⟨k, hik, hkj.trans (Nat.le_succ j), hkdrop⟩
      · have hji : j ≤ i := Nat.le_of_not_gt hij'
        have hij_le : i ≤ j := Nat.le_of_lt_succ hij
        have hi_eq : i = j := le_antisymm hij_le hji
        subst i
        exact ⟨j, le_rfl, le_rfl, hdrop⟩

/-- Every inversion pair contains an adjacent descent between its endpoints. -/
theorem exists_adjacentDescent_of_rifflePattern (n : ℕ) (σ : Equiv.Perm (Fin n))
    {i j : Fin n} (hpattern : rifflePattern n σ i j) :
    ∃ k : ℕ, (i : ℕ) ≤ k ∧ k + 1 ≤ (j : ℕ) ∧
      ∃ hk : k + 1 < n,
        σ ⟨k + 1, hk⟩ < σ ⟨k, Nat.lt_of_succ_lt hk⟩ := by
  rcases hpattern with ⟨hij, hdrop⟩
  let f : ℕ → Fin n := fun t => if ht : t < n then σ ⟨t, ht⟩ else σ i
  have hdropNat : f j < f i := by
    simp [f, i.isLt, j.isLt, hdrop]
  rcases exists_adjacent_drop_nat f (show (i : ℕ) < (j : ℕ) from hij) hdropNat with
    ⟨k, hik, hkj, hkdrop⟩
  have hk : k + 1 < n := hkj.trans_lt j.isLt
  refine ⟨k, hik, hkj, hk, ?_⟩
  have hk0 : k < n := Nat.lt_of_succ_lt hk
  simpa [f, hk, hk0] using hkdrop



/-- A labeling sorts to `σ` iff the labels, read in the order prescribed by
`σ`, form a monotone sequence with strict increases across the inversion
pattern of `σ`. -/
theorem riffleSort_eq_iff_patternCompatible (a n : ℕ) (labels : RiffleLabels a n)
    (σ : Equiv.Perm (Fin n)) :
    riffleSort a n labels = σ ↔
      patternCompatible a n (rifflePattern n σ) (labels ∘ σ) := by
  constructor
  · intro hsort
    have htuple :
        Monotone (labels ∘ σ) ∧
          ∀ i j, i < j → labels (σ i) = labels (σ j) → σ i < σ j := by
      exact (Tuple.eq_sort_iff (f := labels) (σ := σ)).mp hsort.symm
    refine ⟨htuple.1, ?_⟩
    intro i j hpattern
    rcases hpattern with ⟨hij, hinv⟩
    have hle : (labels ∘ σ) i ≤ (labels ∘ σ) j := htuple.1 hij.le
    exact lt_of_le_of_ne hle fun heq => by
      have hσlt : σ i < σ j := htuple.2 i j hij heq
      exact (lt_asymm hσlt hinv).elim
  · intro hcompat
    have htuple :
        Monotone (labels ∘ σ) ∧
          ∀ i j, i < j → labels (σ i) = labels (σ j) → σ i < σ j := by
      refine ⟨hcompat.1, ?_⟩
      intro i j hij heq
      have hσne : σ i ≠ σ j := by
        intro hσeq
        exact hij.ne (σ.injective hσeq)
      rcases lt_or_gt_of_ne hσne with hσlt | hσgt
      · exact hσlt
      · have hstrict : (labels ∘ σ) i < (labels ∘ σ) j :=
          hcompat.2 i j ⟨hij, hσgt⟩
        have hstrict' : labels (σ i) < labels (σ j) := hstrict
        rw [heq] at hstrict'
        exact (lt_irrefl _ hstrict').elim
    exact ((Tuple.eq_sort_iff (f := labels) (σ := σ)).mpr htuple).symm

/-- For monotone label sequences, requiring strict increases across all
inversion pairs is equivalent to requiring them across intervals containing an
adjacent descent. -/
theorem patternCompatible_rifflePattern_iff_descentIntervalPattern (a n : ℕ)
    (σ : Equiv.Perm (Fin n)) (seq : RiffleLabels a n) :
    patternCompatible a n (rifflePattern n σ) seq ↔
      patternCompatible a n (riffleDescentIntervalPattern n σ) seq := by
  constructor
  · intro hcompat
    refine ⟨hcompat.1, ?_⟩
    intro i j hpattern
    rcases hpattern with ⟨_hij, k, hik, hkj, hk, hdesc⟩
    let lo : Fin n := ⟨k, Nat.lt_of_succ_lt hk⟩
    let hi : Fin n := ⟨k + 1, hk⟩
    have hlohi : lo < hi := by
      change k < k + 1
      exact Nat.lt_succ_self k
    have hleft : seq i ≤ seq lo := by
      apply hcompat.1
      change (i : ℕ) ≤ k
      exact hik
    have hright : seq hi ≤ seq j := by
      apply hcompat.1
      change k + 1 ≤ (j : ℕ)
      exact hkj
    have hstrict : seq lo < seq hi := hcompat.2 lo hi ⟨hlohi, hdesc⟩
    exact lt_of_le_of_lt hleft (lt_of_lt_of_le hstrict hright)
  · intro hcompat
    refine ⟨hcompat.1, ?_⟩
    intro i j hpattern
    rcases hpattern with ⟨hij, hdrop⟩
    rcases exists_adjacentDescent_of_rifflePattern n σ ⟨hij, hdrop⟩ with
      ⟨k, hik, hkj, hk, hdesc⟩
    exact hcompat.2 i j ⟨hij, k, hik, hkj, hk, hdesc⟩



/-- The number of riffle labelings producing `σ` is determined by the riffle
pattern of `σ`. -/
theorem count_determined_by_piles (a n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (Finset.univ.filter (fun labels : RiffleLabels a n => riffleSort a n labels = σ)).card =
      rifflePatternCount a n (rifflePattern n σ) := by
  classical
  let e :
      {labels : RiffleLabels a n // riffleSort a n labels = σ} ≃
        {seq : RiffleLabels a n // patternCompatible a n (rifflePattern n σ) seq} :=
    (labelsEquivSortedSeq a n σ).subtypeEquiv fun labels => by
      change riffleSort a n labels = σ ↔
        patternCompatible a n (rifflePattern n σ) (labels ∘ σ)
      exact riffleSort_eq_iff_patternCompatible a n labels σ
  calc
    (Finset.univ.filter (fun labels : RiffleLabels a n => riffleSort a n labels = σ)).card =
        Fintype.card {labels : RiffleLabels a n // riffleSort a n labels = σ} := by
      exact (Fintype.card_subtype fun labels : RiffleLabels a n =>
        riffleSort a n labels = σ).symm
    _ = Fintype.card
        {seq : RiffleLabels a n // patternCompatible a n (rifflePattern n σ) seq} :=
      Fintype.card_congr e
    _ = rifflePatternCount a n (rifflePattern n σ) := by
      rw [rifflePatternCount]
      exact Fintype.card_subtype fun seq : RiffleLabels a n =>
        patternCompatible a n (rifflePattern n σ) seq

/-- The same fiber count expressed using only the adjacent descent interval
pattern of the target permutation. -/
theorem count_determined_by_descents (a n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (Finset.univ.filter (fun labels : RiffleLabels a n => riffleSort a n labels = σ)).card =
      rifflePatternCount a n (riffleDescentIntervalPattern n σ) := by
  rw [count_determined_by_piles]
  rw [rifflePatternCount, rifflePatternCount]
  congr 1
  ext seq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact patternCompatible_rifflePattern_iff_descentIntervalPattern a n σ seq











/--
GSR distribution formula: under the uniform choice of one of the `a^n` label
assignments, the probability of a permutation is its riffle-pattern fiber count
divided by `a^n`.
-/
theorem gsrShuffleProbability_eq_rifflePatternCount (a n : ℕ) [NeZero a]
    (σ : Equiv.Perm (Fin n)) :
    gsrShuffleProbability a n σ =
      (rifflePatternCount a n (riffleDescentIntervalPattern n σ) : ℚ≥0) /
        ((a ^ n : ℕ) : ℚ≥0) := by
  simp [gsrShuffleProbability, Finset.dens, count_determined_by_descents,
    RiffleLabels]

/-- The GSR shuffle probabilities over all permutations have total mass one. -/
theorem gsrShuffleProbability_sum (a n : ℕ) [NeZero a] :
    (∑ σ : Equiv.Perm (Fin n), gsrShuffleProbability a n σ) = 1 := by
  classical
  have h := Finset.dens_eq_sum_dens_fiberwise
    (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))
    (t := (Finset.univ : Finset (RiffleLabels a n)))
    (f := fun labels : RiffleLabels a n => riffleSort a n labels)
    (by intro labels _; exact Finset.mem_univ _)
  simpa [gsrShuffleProbability] using h.symm



end ProofsInTheBook.Chapter29

open ProofsInTheBook.Chapter29

theorem solution (a n : ℕ) [NeZero a] :
    (∀ σ : Equiv.Perm (Fin n),
      gsrShuffleProbability a n σ =
        (rifflePatternCount a n (riffleDescentIntervalPattern n σ) : ℚ≥0) /
          ((a ^ n : ℕ) : ℚ≥0)) ∧
      (∑ σ : Equiv.Perm (Fin n), gsrShuffleProbability a n σ) = 1 :=
  ⟨gsrShuffleProbability_eq_rifflePatternCount a n,
    gsrShuffleProbability_sum a n⟩
