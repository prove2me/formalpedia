-- Prove2me | Definitions.Def_ProofsInTheBook_Chapter29
-- name    : ProofsInTheBook_Chapter29
-- status  : Definition
-- author  : @xiangyazi24
-- created : 2026-09-12T15:57:14.091213+00:00
-- url     : https://prove2.me/theorems/039e298f-9d44-4324-8366-fc551314b02d
-- title:
--   Stable riffle labels, descent constraints, and shuffle probabilities
-- statement:
--   For natural numbers $a,n$, a riffle labeling assigns to each of $n$ indexed cards a label in $\operatorname{Fin}(a)$. Cards are ordered by increasing label, with the original index breaking ties. The resulting ordering is represented by a permutation $\sigma$.
--
--   For positions $i<j$, the inversion pattern records $\sigma(j)<\sigma(i)$; the descent-interval pattern records an adjacent descent somewhere between $i$ and $j$. A compatible sorted label sequence is nondecreasing and is strictly increasing across every pair required by the chosen pattern. Its finite cardinality is the pattern count. Relabeling coordinates by $\sigma$ identifies original-card labelings with sorted-position label sequences.
--
--   For $a>0$, the GSR probability of $\sigma$ is the fraction of all $a^n$ labelings whose stable sort is $\sigma$:
--   $$P_{a,n}(\sigma)=\frac{|\{\ell:\operatorname{Fin}(n)\to\operatorname{Fin}(a):\operatorname{riffleSort}(\ell)=\sigma\}|}{a^n}.$$
--   The definition uses finite-set density in the nonnegative rationals, including its zero-denominator convention.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 31, “Shuffling cards”, pp. 219–228 (https://doi.org/10.1007/978-3-662-57265-8_31). Original definition source: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter29.lean#L34. The generated bundle retains definitions and supporting declarations from this source; the book citation identifies their topic rather than asserting that each auxiliary structure appears in the book.

import Mathlib

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

abbrev RiffleLabels (a n : ℕ) : Type :=
  Fin n → Fin a



































/-- The canonical permutation from a riffle labeling: sort cards by their pile
labels using Mathlib's `Tuple.sort` (which breaks ties by the original index).
This is the concrete `permFromLabels` used in the GSR count. -/
noncomputable def riffleSort (a n : ℕ) (labels : RiffleLabels a n) :
    Equiv.Perm (Fin n) :=
  Tuple.sort labels











/--
The stable riffle order induced by a label assignment: card `i` comes before
card `j` in the shuffled deck iff `labels i < labels j`, or `labels i = labels j`
and `i < j` (within-pile stability).
-/
def riffleOrder (a n : ℕ) (labels : RiffleLabels a n) (i j : Fin n) : Prop :=
  labels i < labels j ∨ (labels i = labels j ∧ i < j)

instance (a n : ℕ) (labels : RiffleLabels a n) : DecidableRel (riffleOrder a n labels) :=
  fun i j => by unfold riffleOrder; exact inferInstance











/-- The inversion pattern of a target riffle permutation, written in shuffled
position coordinates.  A compatible sorted label sequence must strictly increase
across every such pair. -/
def rifflePattern (n : ℕ) (σ : Equiv.Perm (Fin n)) (i j : Fin n) : Prop :=
  i < j ∧ σ j < σ i

/-- The interval form of the adjacent descent pattern.  It records that the
open interval between two shuffled positions contains an adjacent descent of
`σ`.  This is determined by the usual descent set of `σ`. -/
def riffleDescentIntervalPattern (n : ℕ) (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    Prop :=
  i < j ∧
    ∃ k : ℕ, (i : ℕ) ≤ k ∧ k + 1 ≤ (j : ℕ) ∧
      ∃ hk : k + 1 < n,
        σ ⟨k + 1, hk⟩ < σ ⟨k, Nat.lt_of_succ_lt hk⟩

/-- A sorted label sequence compatible with a target riffle pattern. -/
def patternCompatible (a n : ℕ) (pattern : Fin n → Fin n → Prop)
    (seq : RiffleLabels a n) : Prop :=
  Monotone seq ∧ ∀ i j : Fin n, pattern i j → seq i < seq j





/-- Precompose labels by a target permutation.  This changes from original-card
coordinates to shuffled-position coordinates. -/
def labelsEquivSortedSeq (a n : ℕ) (σ : Equiv.Perm (Fin n)) :
    RiffleLabels a n ≃ RiffleLabels a n where
  toFun labels := labels ∘ σ
  invFun seq := seq ∘ σ.symm
  left_inv labels := by
    funext card
    simp [Function.comp_apply]
  right_inv seq := by
    funext card
    simp [Function.comp_apply]





/-- The number of sorted label sequences compatible with a fixed riffle
pattern.  This is the Bayer-Diaconis count written as a fiber over the
descent/inversion pattern, rather than as a closed binomial expression. -/
noncomputable def rifflePatternCount (a n : ℕ) (pattern : Fin n → Fin n → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter fun seq : RiffleLabels a n =>
    patternCompatible a n pattern seq).card











/-- The uniform GSR probability of obtaining `σ` from an `(a,n)` label shuffle. -/
noncomputable def gsrShuffleProbability (a n : ℕ) (σ : Equiv.Perm (Fin n)) : ℚ≥0 :=
  (Finset.univ.filter (fun labels : RiffleLabels a n => riffleSort a n labels = σ)).dens









end ProofsInTheBook.Chapter29


