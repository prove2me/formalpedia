-- Prove2me | Definitions.Def_ProofsInTheBook_Chapter26
-- name    : ProofsInTheBook_Chapter26
-- status  : Definition
-- author  : @xiangyazi24
-- created : 2026-09-12T15:57:10.836975+00:00
-- url     : https://prove2.me/theorems/8b4d88cb-cee7-40a1-94da-e53631cdbd9c
-- title:
--   Lengths of monotone subsequences ending at a position
-- statement:
--   Let $a_0,\ldots,a_{m-1}$ be a finite real sequence and let i be one of its indices. Define $I_i(a)$ to be the set of cardinalities of index subsets S containing i, with every index in S at most i, such that a is strictly increasing on S in the index order. Define $D_i(a)$ in the same way using strictly decreasing values. Then
--   $$\operatorname{lisAt}(a,i)=\max I_i(a),\qquad\operatorname{ldsAt}(a,i)=\max D_i(a).$$
--   Both sets contain 1, from the singleton subset containing i, so these maxima are defined. The sequence may contain repeated values: strict monotonicity is required only within each selected subsequence, and its indices need not be consecutive.
-- source:
--   Mathematical definitions: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter26.lean#L27. Topic: Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 28, “Pigeon-hole and double counting” (https://doi.org/10.1007/978-3-662-57265-8_28). The repository citation specifies the definitions retained here.

import Mathlib

/-!
# Chapter 26: Pigeon-hole and double counting

From "Proofs from THE BOOK":

**Erdős-Szekeres theorem**: Every sequence of n²+1 pairwise distinct real numbers
contains either a strictly increasing subsequence of length ≥ n+1, or a strictly
decreasing subsequence of length ≥ n+1.

*Book proof (Seidenberg 1959).* Assign to each element aᵢ the pair
(length of longest increasing subsequence ending at aᵢ, length of longest
decreasing subsequence ending at aᵢ). These pairs are all distinct: if i < j
and aᵢ < aⱼ then the first component strictly increases; if aᵢ > aⱼ the second
strictly increases. If all labels lie in {1,..,n}², there are only n² distinct
labels — contradicting n²+1 elements by pigeonhole.
-/

namespace ProofsInTheBook.Chapter26

open Finset Function

/-! ### Length of longest monotone subsequence ending at a position -/

/-- The set of valid increasing subsequence lengths ending at position `i`. -/
 noncomputable def incLengths {m : ℕ} (a : Fin m → ℝ) (i : Fin m) : Finset ℕ :=
  (Finset.univ.filter (fun S : Finset (Fin m) =>
    i ∈ S ∧ (∀ j ∈ S, j ≤ i) ∧ StrictMonoOn a (S : Set (Fin m)))).image Finset.card

/-- The set of valid decreasing subsequence lengths ending at position `i`. -/
 noncomputable def decLengths {m : ℕ} (a : Fin m → ℝ) (i : Fin m) : Finset ℕ :=
  (Finset.univ.filter (fun S : Finset (Fin m) =>
    i ∈ S ∧ (∀ j ∈ S, j ≤ i) ∧ StrictAntiOn a (S : Set (Fin m)))).image Finset.card

 lemma singleton_mem_incFilter {m : ℕ} (a : Fin m → ℝ) (i : Fin m) :
    {i} ∈ Finset.univ.filter (fun S : Finset (Fin m) =>
      i ∈ S ∧ (∀ j ∈ S, j ≤ i) ∧ StrictMonoOn a (S : Set (Fin m))) := by
  simp [Finset.mem_filter, StrictMonoOn]

 lemma singleton_mem_decFilter {m : ℕ} (a : Fin m → ℝ) (i : Fin m) :
    {i} ∈ Finset.univ.filter (fun S : Finset (Fin m) =>
      i ∈ S ∧ (∀ j ∈ S, j ≤ i) ∧ StrictAntiOn a (S : Set (Fin m))) := by
  simp [Finset.mem_filter, StrictAntiOn]

 lemma incLengths_nonempty {m : ℕ} (a : Fin m → ℝ) (i : Fin m) :
    (incLengths a i).Nonempty :=
  ⟨1, Finset.mem_image.mpr ⟨{i}, singleton_mem_incFilter a i, Finset.card_singleton _⟩⟩

 lemma decLengths_nonempty {m : ℕ} (a : Fin m → ℝ) (i : Fin m) :
    (decLengths a i).Nonempty :=
  ⟨1, Finset.mem_image.mpr ⟨{i}, singleton_mem_decFilter a i, Finset.card_singleton _⟩⟩

/-- The length of the longest increasing subsequence ending at position `i`. -/
 noncomputable def lisAt {m : ℕ} (a : Fin m → ℝ) (i : Fin m) : ℕ :=
  (incLengths a i).max' (incLengths_nonempty a i)

/-- The length of the longest decreasing subsequence ending at position `i`. -/
 noncomputable def ldsAt {m : ℕ} (a : Fin m → ℝ) (i : Fin m) : ℕ :=
  (decLengths a i).max' (decLengths_nonempty a i)





/-! ### Key injectivity: the (lisAt, ldsAt) label distinguishes positions -/







/-! ### Main theorem -/





end ProofsInTheBook.Chapter26


