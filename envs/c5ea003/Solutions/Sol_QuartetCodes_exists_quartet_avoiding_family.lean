-- Prove2me | solution 1 for QuartetCodes.exists_quartet_avoiding_family
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T17:32:10.001057+00:00
-- url     : https://prove2.me/submissions/65e46d27-56df-4956-b159-66f4b64cfc4f

-- Sol generated from Combinatorics/QuartetCodes.lean
import Mathlib
import Definitions.Def_Combinatorics_Core
import Definitions.Def_Combinatorics_QuartetCodes
import Theorems.Thm_QuartetCodes_card_sameCodeSet
import Theorems.Thm_QuartetCodes_three_mul_qclass_card

/-!
# Quartet signatures as ternary codes

A phylogenetic tree is encoded as a word in the ternary cube indexed by quadruples of leaves: each
four-leaf set admits exactly three resolved quartet types, recorded by `code3` and, for the
caterpillar with leaf order `π`, by `qcode π`.  Under this dictionary the catalog predicate
`AgreementSubtrees.AgreeOn` on a four-leaf set becomes *equality of a letter*
(`qcode_eq_of_agreeOn`), so "no common quartet" becomes "no constant coordinate" in a ternary code.

The file proves:

* the exact ternary balance `three_mul_qclass_card` — each of the three types is displayed by
  exactly one third of all leaf orders;
* the first-moment construction `exists_quartet_avoiding_family` and, via the bridge to split
  systems, the exponential lower bound `exponential_lower_bound`:
  `¬ IsAgreementThreshold (3^v) (4v+2) 4`;
* the explicit optimal five-leaf pair `not_isAgreementThreshold_five_two`;
* the adversarial collapse `card_le_three_of_pairwise_full_distance`: over a ternary alphabet a
  family at full Hamming distance has at most three members, so the weaker avoidance notion is
  genuinely needed.

-- !-- Lab Notes -- !--
## Hypothesis (Hypothesizer)
Quartet avoidance is a coding condition: if the ternary signatures of a family of trees never agree
in a coordinate, no four leaves carry a common quartet, and a random code should provide such
families with only logarithmically many trees per leaf.

## Experiment (Experimenter)
The first-moment computation is exact rather than asymptotic because the three quartet types are
exactly equinumerous under right translation by a transposition inside the quartet
(`qclass_card_eq_of_swap`): the probability that `m+1` random leaf orders agree on a fixed quartet
is exactly `3^{-m}`, and there are at most `n^4` ordered quadruples.

## Analysis (Analyst)
The union bound `n^4 < 3^m` costs one tree per `3^{1/4} ≈ 1.316` leaves.  The companion files show
the truth is nearer `1.7` per tree, so the loss is in the union bound, not in the encoding.

## Critique (Critic)
The bridge lemmas `qcode_eq_{zero,one,two}_iff_restrict` are stated in terms of the catalog's own
`restrict`, so the ternary letter is proved to record the actual restriction of the split system,
not a convenient surrogate; and `card_le_three_of_pairwise_full_distance` rules out the naive
"large minimum distance" reading of the conjecture.
-/

open Finset

open QuartetCodes








/-! ## Caterpillar trees and their quartet signatures -/


variable {n : ℕ}










/-! ## The counting (first-moment) lower bound -/


variable {n k : ℕ}


lemma mem_sameCodeSet {i₀ : Fin k} {a b c d : Fin n} {T : Fin k → Equiv.Perm (Fin n)} :
    T ∈ sameCodeSet i₀ a b c d ↔ ∀ i, qcode (T i) a b c d = qcode (T i₀) a b c d := by
  simp [sameCodeSet]



/-- **Weighted count.**  With `k = m+1` trees, the families sharing a quartet on a fixed set of
four distinct leaves are a `3^m`-th fraction of all families. -/
lemma pow_mul_card_sameCodeSet {m : ℕ} {a b c d : Fin n} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (i₀ : Fin (m + 1)) :
    3 ^ m * (sameCodeSet i₀ a b c d).card = Fintype.card (Equiv.Perm (Fin n)) ^ (m + 1) := by
  have hcls := three_mul_qclass_card hab hac had hbc hbd hcd 0
  rw [card_sameCodeSet hab hac had hbc hbd hcd i₀, ← hcls, mul_pow]
  ring


lemma card_distinctQuads_le (n : ℕ) : (distinctQuads n).card ≤ n ^ 4 := by
  have h := Finset.card_filter_le (Finset.univ : Finset (Fin n × Fin n × Fin n × Fin n))
    (fun q => q.1 ≠ q.2.1 ∧ q.1 ≠ q.2.2.1 ∧ q.1 ≠ q.2.2.2 ∧ q.2.1 ≠ q.2.2.1 ∧ q.2.1 ≠ q.2.2.2 ∧
      q.2.2.1 ≠ q.2.2.2)
  calc (distinctQuads n).card ≤ (Finset.univ : Finset (Fin n × Fin n × Fin n × Fin n)).card := h
    _ = n ^ 4 := by simp [Finset.card_univ]; ring



/-! ## Bridge to the split-system language of `Combinatorics.Core` -/


open AgreementSubtrees

variable {n : ℕ}














/-! ## Adversarial check: pure distance in ternary signature space is too weak -/





open QuartetCodes in
theorem solution(n m : ℕ) (h : n ^ 4 < 3 ^ m) :
    ∃ T : Fin (m + 1) → Equiv.Perm (Fin n), ∀ a b c d : Fin n,
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ∃ i j, qcode (T i) a b c d ≠ qcode (T j) a b c d := by
  classical
  set i₀ : Fin (m + 1) := ⟨0, Nat.succ_pos m⟩ with hi₀
  set M := Fintype.card (Equiv.Perm (Fin n)) with hM
  -- the union of the bad events
  set Bad : Finset (Fin (m + 1) → Equiv.Perm (Fin n)) :=
    (distinctQuads n).biUnion (fun q => sameCodeSet i₀ q.1 q.2.1 q.2.2.1 q.2.2.2) with hBad
  have hcard : 3 ^ m * Bad.card ≤ n ^ 4 * M ^ (m + 1) := by
    have h1 : Bad.card ≤ ∑ q ∈ distinctQuads n,
        (sameCodeSet i₀ q.1 q.2.1 q.2.2.1 q.2.2.2).card := Finset.card_biUnion_le
    have h2 : 3 ^ m * Bad.card ≤ ∑ q ∈ distinctQuads n,
        3 ^ m * (sameCodeSet i₀ q.1 q.2.1 q.2.2.1 q.2.2.2).card := by
      rw [← Finset.mul_sum]
      exact Nat.mul_le_mul_left _ h1
    have h3 : ∀ q ∈ distinctQuads n,
        3 ^ m * (sameCodeSet i₀ q.1 q.2.1 q.2.2.1 q.2.2.2).card = M ^ (m + 1) := by
      intro q hq
      simp only [distinctQuads, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hq
      exact pow_mul_card_sameCodeSet h1 h2 h3 h4 h5 h6 i₀
    calc 3 ^ m * Bad.card ≤ ∑ q ∈ distinctQuads n,
          3 ^ m * (sameCodeSet i₀ q.1 q.2.1 q.2.2.1 q.2.2.2).card := h2
      _ = ∑ _q ∈ distinctQuads n, M ^ (m + 1) := Finset.sum_congr rfl h3
      _ = (distinctQuads n).card * M ^ (m + 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ n ^ 4 * M ^ (m + 1) := Nat.mul_le_mul_right _ (card_distinctQuads_le n)
  have hMpos : 0 < M ^ (m + 1) := pow_pos (Fintype.card_pos) _
  have hlt : Bad.card < M ^ (m + 1) := by
    by_contra hcon
    push_neg at hcon
    have : 3 ^ m * M ^ (m + 1) ≤ n ^ 4 * M ^ (m + 1) :=
      le_trans (Nat.mul_le_mul_left _ hcon) hcard
    have := Nat.le_of_mul_le_mul_right this hMpos
    omega
  have huniv : (Finset.univ : Finset (Fin (m + 1) → Equiv.Perm (Fin n))).card = M ^ (m + 1) := by
    simp [Finset.card_univ, hM]
  have : ∃ T : Fin (m + 1) → Equiv.Perm (Fin n), T ∉ Bad := by
    by_contra hcon
    push_neg at hcon
    have : (Finset.univ : Finset (Fin (m + 1) → Equiv.Perm (Fin n))) ⊆ Bad :=
      fun T _ => hcon T
    have := Finset.card_le_card this
    omega
  obtain ⟨T, hT⟩ := this
  refine ⟨T, fun a b c d hab hac had hbc hbd hcd => ?_⟩
  by_contra hcon
  push_neg at hcon
  refine hT ?_
  rw [hBad, Finset.mem_biUnion]
  refine ⟨(a, b, c, d), ?_, ?_⟩
  · simp [distinctQuads, hab, hac, had, hbc, hbd, hcd]
  · exact mem_sameCodeSet.2 (fun i => hcon i i₀)
