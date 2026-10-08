-- Prove2me | solution 1 for ProofsInTheBook.Chapter38.chapter38
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T16:13:12.884263+00:00
-- url     : https://prove2.me/submissions/709c036f-0753-4e58-8b46-8adbbbd5e1ab

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter38


/-!
# Chapter 38: Communicating without errors

From "Proofs from THE BOOK":

**Intended chapter content.** The chapter discusses error-correcting codes,
including the Singleton bound, the Hamming sphere-packing bound, the
Gilbert-Varshamov greedy existence bound, and the analytic Shannon capacity
formula `C = 1 - H(p)` for the binary symmetric channel.

This file formalizes the finite combinatorial bounds.  The Shannon capacity
statement is not claimed here: it requires entropy and asymptotic channel
capacity analysis, and is recorded as an honest point-17 gap/frontier rather
than as a weakened Lean theorem.
-/

namespace ProofsInTheBook.Chapter38

open Finset

/-!
### Words, Hamming balls, and volume

For a `q`-ary alphabet we use `Fin q`.  The Hamming ball volume is formalized
as the cardinality of a ball; the usual closed form
`∑ i ≤ r, (n.choose i) * (q - 1)^i` is not needed for the three finite bounds.
-/























lemma hammingBall_card_eq {q n radius : ℕ} (x y : QaryWord q n) :
    (hammingBall q n radius x).card = (hammingBall q n radius y).card := by
  classical
  calc
    (hammingBall q n radius x).card =
        Fintype.card {word : QaryWord q n // word ∈ hammingBall q n radius x} :=
      (Fintype.card_coe _).symm
    _ = Fintype.card {word : QaryWord q n // word ∈ hammingBall q n radius y} :=
      Fintype.card_congr (hammingBallEquiv x y)
    _ = (hammingBall q n radius y).card :=
      Fintype.card_coe _

lemma hammingBall_card_eq_qaryHammingBallVolume {q n radius : ℕ} (hq : 0 < q)
    (center : QaryWord q n) :
    (hammingBall q n radius center).card = qaryHammingBallVolume q n radius := by
  rw [qaryHammingBallVolume, dif_pos hq]
  exact hammingBall_card_eq center (zeroQaryWord (q := q) (n := n) hq)

/-!
### Unique decoding

Hamming balls of radius `t` around distinct codewords are disjoint when the
minimum distance is greater than `2t`.
-/

theorem unique_decode_of_two_mul_radius_lt_distance {q n t d : ℕ}
    {code : Finset (QaryWord q n)}
    (hmin : ∀ c₁ ∈ code, ∀ c₂ ∈ code, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂)
    (hd : 2 * t < d) {received c₁ c₂ : QaryWord q n}
    (hc₁ : c₁ ∈ code) (hc₂ : c₂ ∈ code)
    (hr₁ : hammingDist c₁ received ≤ t) (hr₂ : hammingDist c₂ received ≤ t) :
    c₁ = c₂ := by
  by_contra hne
  have hdist_lower : d ≤ hammingDist c₁ c₂ := hmin c₁ hc₁ c₂ hc₂ hne
  have hdist_upper : hammingDist c₁ c₂ ≤ 2 * t := by
    have htri : hammingDist c₁ c₂ ≤ hammingDist c₁ received + hammingDist received c₂ :=
      hammingDist_triangle c₁ received c₂
    have hr₂' : hammingDist received c₂ ≤ t := by
      simpa [hammingDist_comm] using hr₂
    nlinarith
  omega

/-!
### Singleton bound

If a `q`-ary length-`n` code has minimum distance at least `d`, then puncturing
to the first `n + 1 - d` coordinates is injective on the code.  Hence
`|C| ≤ q^(n + 1 - d)`, the natural-number rendering of `q^{n-d+1}`.
-/

lemma hammingDist_le_of_eq_on_prefix {q n d : ℕ} (hd : 0 < d)
    {x y : QaryWord q n}
    (heq : ∀ i : Fin n, (i : ℕ) < n + 1 - d → x i = y i) :
    hammingDist x y ≤ d - 1 := by
  classical
  unfold hammingDist
  let m := n + 1 - d
  have hsupp_subset :
      (Finset.univ.filter fun i : Fin n => x i ≠ y i) ⊆
        (Finset.univ.filter fun i : Fin n => ¬ (i : ℕ) < m) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    exact fun hlt => hi (heq i (by simpa [m] using hlt))
  have hdist_le :
      (Finset.univ.filter fun i : Fin n => x i ≠ y i).card ≤
        (Finset.univ.filter fun i : Fin n => ¬ (i : ℕ) < m).card :=
    Finset.card_le_card hsupp_subset
  have hmle : m ≤ n := by
    omega
  have hfront :
      (Finset.univ.filter fun i : Fin n => (i : ℕ) < m).card = m := by
    calc
      (Finset.univ.filter fun i : Fin n => (i : ℕ) < m).card = min n m := by
        simpa [m] using (Fin.card_filter_val_lt (n := n) (m := m))
      _ = m := min_eq_right hmle
  have hsplit :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun i : Fin n => (i : ℕ) < m)
  have hback :
      (Finset.univ.filter fun i : Fin n => ¬ (i : ℕ) < m).card ≤ d - 1 := by
    have htotal :
        m + (Finset.univ.filter fun i : Fin n => ¬ (i : ℕ) < m).card = n := by
      simpa [hfront] using hsplit
    omega
  exact hdist_le.trans hback

theorem singleton_bound {q n d : ℕ} {code : Finset (QaryWord q n)}
    (hd : 0 < d)
    (hmin : ∀ c₁ ∈ code, ∀ c₂ ∈ code, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂) :
    code.card ≤ q ^ (n + 1 - d) := by
  classical
  let m := n + 1 - d
  have hmle : m ≤ n := by
    omega
  let proj := fun (w : QaryWord q n) (i : Fin m) => w (Fin.castLE hmle i)
  have hinj : Set.InjOn proj (code : Set (QaryWord q n)) := by
    intro x hx y hy hxy
    by_contra hne
    have hdist_lower : d ≤ hammingDist x y := hmin x hx y hy hne
    have hdist_upper : hammingDist x y ≤ d - 1 := by
      apply hammingDist_le_of_eq_on_prefix (q := q) (n := n) (d := d) hd
      intro i hi
      have hi' : (i : ℕ) < m := by
        simpa [m] using hi
      let j := (⟨(i : ℕ), hi'⟩ : Fin m)
      have hj : Fin.castLE hmle j = i := by
        ext
        simp [j]
      have hprefix := congr_fun hxy j
      simpa [proj, hj] using hprefix
    omega
  calc
    code.card = (code.image proj).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card (QaryWord q m) :=
      Finset.card_le_univ _
    _ = q ^ (n + 1 - d) := by
      simp [QaryWord, m]

/-!
### Hamming sphere-packing bound

For minimum distance at least `d` and `2t < d`, radius-`t` Hamming balls about
codewords are pairwise disjoint, so their total volume is at most the ambient
space size `q^n`.
-/

theorem hamming_sphere_packing_bound {q n t d : ℕ} (hq : 0 < q)
    {code : Finset (QaryWord q n)}
    (hmin : ∀ c₁ ∈ code, ∀ c₂ ∈ code, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂)
    (hd : 2 * t < d) :
    code.card * qaryHammingBallVolume q n t ≤ q ^ n := by
  classical
  let ball : QaryWord q n → Finset (QaryWord q n) := fun c => hammingBall q n t c
  have hpair : (code : Set (QaryWord q n)).PairwiseDisjoint ball := by
    rw [Finset.pairwiseDisjoint_iff]
    intro c₁ hc₁ c₂ hc₂ hinter
    rcases hinter with ⟨received, hreceived⟩
    have hr₁ : hammingDist c₁ received ≤ t := by
      simpa [ball, hammingBall] using (Finset.mem_inter.mp hreceived).1
    have hr₂ : hammingDist c₂ received ≤ t := by
      simpa [ball, hammingBall] using (Finset.mem_inter.mp hreceived).2
    exact unique_decode_of_two_mul_radius_lt_distance hmin hd hc₁ hc₂ hr₁ hr₂
  have hcard_union :
      (code.biUnion ball).card = code.card * qaryHammingBallVolume q n t := by
    calc
      (code.biUnion ball).card = ∑ c ∈ code, (ball c).card :=
        Finset.card_biUnion hpair
      _ = code.card * qaryHammingBallVolume q n t :=
        Finset.sum_const_nat (s := code) (m := qaryHammingBallVolume q n t)
          (f := fun c => (ball c).card)
          (by
            intro c _hc
            exact hammingBall_card_eq_qaryHammingBallVolume hq c)
  have hunion_le : (code.biUnion ball).card ≤ q ^ n := by
    calc
      (code.biUnion ball).card ≤ Fintype.card (QaryWord q n) :=
        Finset.card_le_univ _
      _ = q ^ n := by
        simp [QaryWord]
  rwa [← hcard_union]

/-!
### Gilbert-Varshamov greedy existence bound

A maximum-cardinality code with minimum distance at least `d` must cover the
whole ambient space by balls of radius `d - 1`; otherwise one more word could
be inserted.  Counting that cover gives the finite Gilbert-Varshamov bound.
-/

theorem gilbert_varshamov_existence {q n d : ℕ} (hq : 0 < q) :
    ∃ code : Finset (QaryWord q n),
      (∀ c₁ ∈ code, ∀ c₂ ∈ code, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂) ∧
        q ^ n ≤ code.card * qaryHammingBallVolume q n (d - 1) := by
  classical
  let validCodes : Finset (Finset (QaryWord q n)) :=
    Finset.univ.filter fun code =>
      ∀ c₁ ∈ code, ∀ c₂ ∈ code, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂
  have hvalidCodes_nonempty : validCodes.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [validCodes]
  obtain ⟨code, hcode_mem, hmax⟩ :=
    Finset.exists_max_image validCodes (fun code : Finset (QaryWord q n) => code.card)
      hvalidCodes_nonempty
  have hcode :
      ∀ c₁ ∈ code, ∀ c₂ ∈ code, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂ := by
    simpa [validCodes] using hcode_mem
  let ball : QaryWord q n → Finset (QaryWord q n) :=
    fun c => hammingBall q n (d - 1) c
  have hcover : (Finset.univ : Finset (QaryWord q n)) ⊆ code.biUnion ball := by
    intro w _hw
    by_contra hnot_covered
    have hfar : ∀ c ∈ code, ¬ hammingDist c w ≤ d - 1 := by
      intro c hc hle
      exact hnot_covered (Finset.mem_biUnion.mpr ⟨c, hc, by simpa [ball, hammingBall] using hle⟩)
    have hw_not_mem : w ∉ code := by
      intro hw_mem
      exact hfar w hw_mem (by simp)
    have hinsert_valid :
        ∀ c₁ ∈ insert w code, ∀ c₂ ∈ insert w code, c₁ ≠ c₂ →
          d ≤ hammingDist c₁ c₂ := by
      intro c₁ hc₁ c₂ hc₂ hne
      rw [mem_insert] at hc₁ hc₂
      rcases hc₁ with hc₁eq | hc₁
      · subst c₁
        rcases hc₂ with hc₂eq | hc₂
        · subst c₂
          exact (hne rfl).elim
        · have hfar₂ := hfar c₂ hc₂
          have hdist : d ≤ hammingDist c₂ w := by
            omega
          simpa [hammingDist_comm] using hdist
      · rcases hc₂ with hc₂eq | hc₂
        · subst c₂
          have hfar₁ := hfar c₁ hc₁
          omega
        · exact hcode c₁ hc₁ c₂ hc₂ hne
    have hinsert_mem : insert w code ∈ validCodes := by
      change insert w code ∈
        (Finset.univ.filter fun code : Finset (QaryWord q n) =>
          ∀ c₁ ∈ code, ∀ c₂ ∈ code, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂)
      exact mem_filter.mpr ⟨mem_univ _, hinsert_valid⟩
    have hle := hmax (insert w code) hinsert_mem
    have hlt : code.card < (insert w code).card := by
      rw [Finset.card_insert_of_notMem hw_not_mem]
      omega
    omega
  have hsum_eq :
      ∑ c ∈ code, (ball c).card = code.card * qaryHammingBallVolume q n (d - 1) :=
    Finset.sum_const_nat (s := code) (m := qaryHammingBallVolume q n (d - 1))
      (f := fun c => (ball c).card)
      (by
        intro c _hc
        exact hammingBall_card_eq_qaryHammingBallVolume hq c)
  refine ⟨code, hcode, ?_⟩
  calc
    q ^ n = (Finset.univ : Finset (QaryWord q n)).card := by
      simp [QaryWord]
    _ ≤ (code.biUnion ball).card :=
      Finset.card_le_card hcover
    _ ≤ ∑ c ∈ code, (ball c).card :=
      Finset.card_biUnion_le
    _ = code.card * qaryHammingBallVolume q n (d - 1) :=
      hsum_eq

/-!
### Chapter theorem

The finite, combinatorial Chapter 38 content proved here consists of:

* Singleton: `|C| ≤ q^(n+1-d)`.
* Hamming sphere-packing: `|C| * Vol(t) ≤ q^n` when `2t < d`.
* Gilbert-Varshamov existence: some distance-`d` code satisfies
  `q^n ≤ |C| * Vol(d-1)`.

The Shannon capacity formula remains the documented analytic frontier above.
-/



end ProofsInTheBook.Chapter38

open Finset
open ProofsInTheBook.Chapter38

theorem solution {q n t d : ℕ} (hq : 0 < q) {code : Finset (QaryWord q n)}
    (hmin : ∀ c₁ ∈ code, ∀ c₂ ∈ code, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂)
    (hd_pos : 0 < d) (ht : 2 * t < d) :
    code.card ≤ q ^ (n + 1 - d) ∧
      code.card * qaryHammingBallVolume q n t ≤ q ^ n ∧
        ∃ gvCode : Finset (QaryWord q n),
          (∀ c₁ ∈ gvCode, ∀ c₂ ∈ gvCode, c₁ ≠ c₂ → d ≤ hammingDist c₁ c₂) ∧
            q ^ n ≤ gvCode.card * qaryHammingBallVolume q n (d - 1) := by
  exact ⟨singleton_bound hd_pos hmin,
    hamming_sphere_packing_bound hq hmin ht,
    gilbert_varshamov_existence hq⟩
