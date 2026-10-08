-- Prove2me | solution 1 for ProofsInTheBook.Chapter39.chapter39_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T17:09:18.466005+00:00
-- url     : https://prove2.me/submissions/2d8ef2c5-6c43-4b4b-bc83-aaf5d359c6b9

import Init
import Mathlib
import Mathlib.Data.Fin.Tuple.Sort
import Definitions.Def_P2MAssembly_Chapter39


/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.Chapter39 -/
section
set_option autoImplicit true


/-!
# Chapter 39: The chromatic number of Kneser graphs

From "Proofs from THE BOOK":

**Lovász's theorem**: χ(KG(n,k)) = n - 2k + 2.

The book presents Bárány's short proof using the Borsuk-Ulam theorem:
if KG(n,k) were (n-2k+1)-colorable, one could construct a continuous
map S^{n-2k+1} → ℝ^{n-2k} with no antipodal pair mapping to the same
point, contradicting Borsuk-Ulam.

Formalization status: this file closes the graph-combinatorial layer.  It
defines the Kneser graph, proves basic cardinality and edge facts, proves the
explicit `n - 2*k + 2` coloring upper bound, handles the `n = 2*k` lower-bound
edge case, and formalizes Matoušek's finite reduction from a too-small Kneser
coloring to a Tucker-labeling counterexample.

Gap to the full book theorem: the missing upstream theorem can be supplied by
either the analytic Borsuk-Ulam route or the discrete Matoušek/Tucker route.
The local Mathlib checkout has general topological and abstract/geometric
simplicial-complex infrastructure, but no Borsuk-Ulam theorem, Tucker lemma,
Ky Fan lemma, octahedral sphere labeling theorem, or ready-made bridge from
too-small Kneser colorings to a forbidden antipodal/complementary labeling.

The remaining upstream gap is now the finite Ky Fan boundary-parity count,
formalized in two equivalent ways: `KyFanPrefixParityStatement` says that the
positive-first alternating signed-permutation prefix chains are odd, while
`KyFanPrefixModFourStatement` says that both orientations together have
cardinality `2 mod 4`.  This file proves the Matoušek construction from a
hypothetical `(n - 2*k + 1)`-coloring of `KG(n,k)` to a Tucker counterexample,
proves low-dimensional Tucker cases, packages them into an unconditional
low-dimensional Lovász theorem, proves the one-dimensional Ky Fan prefix-parity
count and the vacuous two-dimensional Ky Fan prefix-parity case, and proves
either Ky Fan parity frontier implies
`TuckerLemmaStatement → chapter39`.
-/

namespace ProofsInTheBook.Chapter39



















































private theorem kneserColor_proper {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (a b : KneserVertex n k) (hadj : (kneserGraph n k).Adj a b) :
    kneserColor hk hn a ≠ kneserColor hk hn b := by
  intro heq
  have hdisj : Disjoint a.1 b.1 := hadj.2
  have hma_mem : KneserVertex.min' hk a ∈ a.1 := Finset.min'_mem _ _
  have hmb_mem : KneserVertex.min' hk b ∈ b.1 := Finset.min'_mem _ _
  have hne_min : (KneserVertex.min' hk a).val ≠ (KneserVertex.min' hk b).val := by
    intro h
    exact Finset.disjoint_left.mp hdisj hma_mem (by rwa [Fin.ext_iff.mpr h])
  simp only [kneserColor, Fin.mk.injEq] at heq
  unfold kneserColorNat at heq
  by_cases ha : (KneserVertex.min' hk a).val ≤ n - 2 * k <;>
    by_cases hb : (KneserVertex.min' hk b).val ≤ n - 2 * k <;>
    simp only [ha, hb, ite_true, ite_false] at heq
  · exact hne_min heq
  · omega
  · omega
  · have ha_neg := ha; have hb_neg := hb
    have ha_sub : ∀ x ∈ (↑a : Finset (Fin n)), n - 2 * k < x.val := by
      intro x hx; by_contra hle; push Not at hle
      exact ha_neg (Nat.le_trans (Finset.min'_le _ _ hx) hle)
    have hb_sub : ∀ x ∈ (↑b : Finset (Fin n)), n - 2 * k < x.val := by
      intro x hx; by_contra hle; push Not at hle
      exact hb_neg (Nat.le_trans (Finset.min'_le _ _ hx) hle)
    have hcard_union : ((↑a : Finset (Fin n)) ∪ ↑b).card = 2 * k := by
      rw [Finset.card_union_of_disjoint hdisj]
      have := a.2; have := b.2; omega
    have hsub : (↑a : Finset (Fin n)) ∪ ↑b ⊆ Finset.univ.filter fun i : Fin n => n - 2 * k < i.val := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        rcases Finset.mem_union.mp hx with h | h
        · exact ha_sub x h
        · exact hb_sub x h⟩
    have hle := Finset.card_le_card hsub
    have hfilt_le : (Finset.univ.filter fun i : Fin n => n - 2 * k < i.val).card +
        (Finset.univ.filter fun i : Fin n => i.val ≤ n - 2 * k).card = n := by
      have := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin n))) (p := fun i => n - 2 * k < i.val)
      simp at this; omega
    have hlow : (Finset.univ.filter fun i : Fin n => i.val ≤ n - 2 * k).card ≥ n - 2 * k + 1 := by
      have : ∀ j : Fin (n - 2 * k + 1), (⟨j.val, by omega⟩ : Fin n) ∈
          Finset.univ.filter fun i : Fin n => i.val ≤ n - 2 * k := by
        intro j; simp; omega
      calc _ ≥ Fintype.card (Fin (n - 2 * k + 1)) := by
            exact Finset.card_le_card_of_injOn (fun j => ⟨j.val, by omega⟩)
              (fun j _ => this j) (fun a _ b _ h => by simp [Fin.ext_iff] at h; exact Fin.ext h)
        _ = n - 2 * k + 1 := Fintype.card_fin _
    omega

theorem kneser_chromatic_upper_bound (n k : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    ∃ C : KneserVertex n k → Fin (n - 2 * k + 2),
      ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b :=
  ⟨kneserColor hk hn, kneserColor_proper hk hn⟩

/-! ### Tucker-lemma route for the hard lower bound -/



namespace SignedSubset









theorem card_antipode {n : ℕ} (X : SignedSubset n) :
    X.antipode.card = X.card := by
  simp [card, antipode, Nat.add_comm]





theorem support_antipode {n : ℕ} (X : SignedSubset n) :
    X.antipode.support = X.support := by
  ext i
  simp [support, antipode, or_comm]





theorem maxSupport_mem_support {n : ℕ} (X : SignedSubset n) (hX : X.Nonzero) :
    X.maxSupport hX ∈ X.support := by
  exact Finset.max'_mem _ _

theorem maxSupport_congr_proof {n : ℕ} (X : SignedSubset n)
    (h₁ h₂ : X.Nonzero) : X.maxSupport h₁ = X.maxSupport h₂ := by
  unfold maxSupport
  congr

theorem maxSupport_antipode {n : ℕ} (X : SignedSubset n) (hX : X.Nonzero) :
    X.antipode.maxSupport ((antipode_nonzero X).mpr hX) = X.maxSupport hX := by
  apply le_antisymm
  · apply Finset.max'_le
    intro y hy
    have hy' : y ∈ X.support := by
      simpa [support_antipode] using hy
    exact Finset.le_max' _ y hy'
  · apply Finset.max'_le
    intro y hy
    have hy' : y ∈ X.antipode.support := by
      simpa [support_antipode] using hy
    exact Finset.le_max' _ y hy'



theorem maxSupportPositive_congr_proof {n : ℕ} (X : SignedSubset n)
    (h₁ h₂ : X.Nonzero) : X.maxSupportPositive h₁ = X.maxSupportPositive h₂ := by
  unfold maxSupportPositive
  rw [maxSupport_congr_proof X h₁ h₂]

theorem maxSupportPositive_antipode {n : ℕ} (X : SignedSubset n) (hX : X.Nonzero) :
    X.antipode.maxSupportPositive ((antipode_nonzero X).mpr hX) =
      !(X.maxSupportPositive hX) := by
  unfold maxSupportPositive
  rw [maxSupport_antipode]
  change decide (X.maxSupport hX ∈ X.neg) = !decide (X.maxSupport hX ∈ X.pos)
  by_cases hpos : X.maxSupport hX ∈ X.pos
  · have hnotneg : X.maxSupport hX ∉ X.neg := by
      intro hneg
      exact (Finset.disjoint_left.mp X.disjoint) hpos hneg
    simp [hpos, hnotneg]
  · have hneg : X.maxSupport hX ∈ X.neg := by
      have hmem := X.maxSupport_mem_support hX
      exact (Finset.mem_union.mp hmem).resolve_left hpos
    simp [hpos, hneg]









theorem side_antipode_not {n : ℕ} (X : SignedSubset n) (positive : Bool) :
    X.antipode.side (!positive) = X.side positive := by
  cases positive <;> simp [side, antipode]

theorem side_disjoint_of_le_not {n : ℕ} {X Y : SignedSubset n}
    (hXY : Le X Y) (positive : Bool) :
    Disjoint (X.side positive) (Y.side (!positive)) := by
  cases positive
  · simp [side]
    exact Disjoint.mono hXY.2 (fun _ h => h) Y.disjoint.symm
  · simp [side]
    exact Disjoint.mono hXY.1 (fun _ h => h) Y.disjoint

theorem eq_of_le_card_eq {n : ℕ} {X Y : SignedSubset n}
    (hXY : Le X Y) (hcard : X.card = Y.card) : X = Y := by
  have hpos_le : X.pos.card ≤ Y.pos.card := Finset.card_le_card hXY.1
  have hneg_le : X.neg.card ≤ Y.neg.card := Finset.card_le_card hXY.2
  have hsum : X.pos.card + X.neg.card = Y.pos.card + Y.neg.card := by
    simpa [card] using hcard
  have hpos_ge : Y.pos.card ≤ X.pos.card := by omega
  have hneg_ge : Y.neg.card ≤ X.neg.card := by omega
  have hpos_eq : X.pos = Y.pos := Finset.eq_of_subset_of_card_le hXY.1 hpos_ge
  have hneg_eq : X.neg = Y.neg := Finset.eq_of_subset_of_card_le hXY.2 hneg_ge
  cases X with
  | mk xpos xneg xdisj =>
      cases Y with
      | mk ypos yneg ydisj =>
          dsimp at hpos_eq hneg_eq
          subst ypos
          subst yneg
          simp

end SignedSubset



namespace NonzeroSignedSubset



end NonzeroSignedSubset



namespace SignedLabel





end SignedLabel















theorem exists_kneserVertexIn_color_eq_minColorInSupport {n k q : ℕ}
    (C : KneserVertex n k → Fin q) {support : Finset (Fin n)}
    (hcard : k ≤ support.card) :
    ∃ A : KneserVertexIn n k support, C A.1 = minColorInSupport C support hcard := by
  classical
  have hmem :
      minColorInSupport C support hcard ∈ colorsInSupport C support :=
    Finset.min'_mem _ _
  rcases Finset.mem_image.mp hmem with ⟨A, _hA, hAeq⟩
  exact ⟨A, hAeq⟩



/--
Key finite step in Matoušek's Tucker reduction: if two disjoint supports both
contain a `k`-subset, then a proper Kneser coloring gives different minimum
colors on the two supports.
-/
theorem minColorInSupport_ne_of_disjoint {n k q : ℕ} (hk : 1 ≤ k)
    (C : KneserVertex n k → Fin q)
    (hC : ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b)
    {left right : Finset (Fin n)}
    (hdisj : Disjoint left right)
    (hleft : k ≤ left.card) (hright : k ≤ right.card) :
    minColorInSupport C left hleft ≠ minColorInSupport C right hright := by
  classical
  obtain ⟨A, hAcolor⟩ := exists_kneserVertexIn_color_eq_minColorInSupport C hleft
  obtain ⟨B, hBcolor⟩ := exists_kneserVertexIn_color_eq_minColorInSupport C hright
  have hABdisj : Disjoint (A.1.1 : Finset (Fin n)) (B.1.1 : Finset (Fin n)) :=
    Disjoint.mono A.2 B.2 hdisj
  have hABne : A.1 ≠ B.1 := by
    intro h
    have hself : Disjoint (A.1.1 : Finset (Fin n)) (A.1.1 : Finset (Fin n)) := by
      simpa [h] using hABdisj
    have hempty : (A.1.1 : Finset (Fin n)) = ∅ := by
      exact (Finset.disjoint_self_iff_empty _).mp hself
    have hzero : (A.1.1 : Finset (Fin n)).card = 0 := by simp [hempty]
    have hAcard : (A.1.1 : Finset (Fin n)).card = k := A.1.2
    omega
  intro hmin
  exact hC A.1 B.1 ⟨hABne, hABdisj⟩ (hAcolor.trans (hmin.trans hBcolor.symm))





theorem matousekSmallSupportLabel_antipode {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (X : SignedSubset n) (hX : X.Nonzero) (hsmall : X.card ≤ 2 * k - 2) :
    matousekSmallSupportLabel hk hn X.antipode ((SignedSubset.antipode_nonzero X).mpr hX)
        (by simpa [SignedSubset.card_antipode] using hsmall) =
      (matousekSmallSupportLabel hk hn X hX hsmall).neg := by
  change SignedLabel.mk
      (X.antipode.maxSupportPositive ((SignedSubset.antipode_nonzero X).mpr hX))
      (matousekSmallSupportIndex hk hn X.antipode ((SignedSubset.antipode_nonzero X).mpr hX)
        (by simpa [SignedSubset.card_antipode] using hsmall)) =
    SignedLabel.mk (!(X.maxSupportPositive hX)) (matousekSmallSupportIndex hk hn X hX hsmall)
  have hpositive :
      X.antipode.maxSupportPositive ((SignedSubset.antipode_nonzero X).mpr hX) =
        !(X.maxSupportPositive hX) :=
    SignedSubset.maxSupportPositive_antipode X hX
  have hindex :
      matousekSmallSupportIndex hk hn X.antipode ((SignedSubset.antipode_nonzero X).mpr hX)
          (by simpa [SignedSubset.card_antipode] using hsmall) =
        matousekSmallSupportIndex hk hn X hX hsmall := by
    apply Fin.ext
    simp [matousekSmallSupportIndex, SignedSubset.card_antipode]
  exact SignedLabel.ext hpositive hindex

theorem matousekSmallSupportIndex_congr_proof {n k : ℕ} (hk : 1 ≤ k)
    (hn : 2 * k ≤ n) (X : SignedSubset n)
    (hX₁ hX₂ : X.Nonzero)
    (hsmall₁ hsmall₂ : X.card ≤ 2 * k - 2) :
    matousekSmallSupportIndex hk hn X hX₁ hsmall₁ =
      matousekSmallSupportIndex hk hn X hX₂ hsmall₂ := by
  apply Fin.ext
  simp [matousekSmallSupportIndex]

theorem matousekSmallSupportLabel_congr_proof {n k : ℕ} (hk : 1 ≤ k)
    (hn : 2 * k ≤ n) (X : SignedSubset n)
    (hX₁ hX₂ : X.Nonzero)
    (hsmall₁ hsmall₂ : X.card ≤ 2 * k - 2) :
    matousekSmallSupportLabel hk hn X hX₁ hsmall₁ =
      matousekSmallSupportLabel hk hn X hX₂ hsmall₂ := by
  apply SignedLabel.ext
  · exact SignedSubset.maxSupportPositive_congr_proof X hX₁ hX₂
  · exact matousekSmallSupportIndex_congr_proof hk hn X hX₁ hX₂ hsmall₁ hsmall₂

theorem matousekSmallSupportLabel_ne_neg_of_le {n k : ℕ} (hk : 1 ≤ k)
    (hn : 2 * k ≤ n) {X Y : SignedSubset n}
    (hX : X.Nonzero) (hY : Y.Nonzero)
    (hXsmall : X.card ≤ 2 * k - 2) (hYsmall : Y.card ≤ 2 * k - 2)
    (hXY : SignedSubset.Le X Y) :
    matousekSmallSupportLabel hk hn X hX hXsmall ≠
      (matousekSmallSupportLabel hk hn Y hY hYsmall).neg := by
  intro hcomp
  have hindex :
      matousekSmallSupportIndex hk hn X hX hXsmall =
        matousekSmallSupportIndex hk hn Y hY hYsmall := by
    have := congrArg SignedLabel.index hcomp
    simpa [matousekSmallSupportLabel, SignedLabel.neg] using this
  have hindex_val := congrArg Fin.val hindex
  have hXpos : 0 < X.card := SignedSubset.card_pos_of_nonzero hX
  have hYpos : 0 < Y.card := SignedSubset.card_pos_of_nonzero hY
  have hcard : X.card = Y.card := by
    simp [matousekSmallSupportIndex] at hindex_val
    omega
  have hXYeq : X = Y := SignedSubset.eq_of_le_card_eq hXY hcard
  subst Y
  have hpositive := congrArg SignedLabel.positive hcomp
  simp [matousekSmallSupportLabel, SignedLabel.neg] at hpositive





theorem decide_lt_swap_eq_not {α : Type*} [LinearOrder α] [DecidableRel ((· < ·) : α → α → Prop)]
    {a b : α} (hne : a ≠ b) : decide (b < a) = !decide (a < b) := by
  by_cases hab : a < b
  · have hba : ¬ b < a := not_lt_of_ge hab.le
    simp [hab, hba]
  · have hba : b < a := lt_of_le_of_ne (le_of_not_gt hab) hne.symm
    simp [hab, hba]



@[simp]
theorem matousekLargeSupportPositive_congr_proof {n k q : ℕ}
    (C : KneserVertex n k → Fin q) (X : SignedSubset n)
    (hlarge₁ hlarge₂ : 2 * k - 1 ≤ X.card) :
    matousekLargeSupportPositive C X hlarge₁ =
      matousekLargeSupportPositive C X hlarge₂ := by
  rfl



theorem matousekLargeSupportPositive_antipode {n k q : ℕ} (hk : 1 ≤ k)
    (C : KneserVertex n k → Fin q)
    (hC : ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b)
    (X : SignedSubset n) (hlarge : 2 * k - 1 ≤ X.card) :
    matousekLargeSupportPositive C X.antipode
        (by simpa [SignedSubset.card_antipode] using hlarge) =
      !(matousekLargeSupportPositive C X hlarge) := by
  by_cases hpos : k ≤ X.pos.card
  · by_cases hneg : k ≤ X.neg.card
    · have hne :
          minColorInSupport C X.pos hpos ≠ minColorInSupport C X.neg hneg :=
        minColorInSupport_ne_of_disjoint hk C hC X.disjoint hpos hneg
      have hswap :
          decide (minColorInSupport C X.neg hneg < minColorInSupport C X.pos hpos) =
            !decide (minColorInSupport C X.pos hpos < minColorInSupport C X.neg hneg) :=
        decide_lt_swap_eq_not hne
      simpa [matousekLargeSupportPositive, SignedSubset.antipode, hpos, hneg] using hswap
    · simp [matousekLargeSupportPositive, SignedSubset.antipode, hpos, hneg]
  · have hside := signedSubset_large_support_has_k_side (X := X) hlarge
    have hneg : k ≤ X.neg.card := hside.resolve_left hpos
    simp [matousekLargeSupportPositive, SignedSubset.antipode, hpos, hneg]



theorem matousekLargeSupportColor_congr_proof {n k q : ℕ}
    (C : KneserVertex n k → Fin q) (X : SignedSubset n)
    (hlarge₁ hlarge₂ : 2 * k - 1 ≤ X.card) :
    matousekLargeSupportColor C X hlarge₁ =
      matousekLargeSupportColor C X hlarge₂ := by
  simp [matousekLargeSupportColor]

theorem matousekLargeSupportColor_antipode {n k q : ℕ} (hk : 1 ≤ k)
    (C : KneserVertex n k → Fin q)
    (hC : ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b)
    (X : SignedSubset n) (hlarge : 2 * k - 1 ≤ X.card) :
    matousekLargeSupportColor C X.antipode
        (by simpa [SignedSubset.card_antipode] using hlarge) =
      matousekLargeSupportColor C X hlarge := by
  have hpositive := matousekLargeSupportPositive_antipode hk C hC X hlarge
  simp [matousekLargeSupportColor, hpositive, SignedSubset.side_antipode_not]



theorem matousekLargeSupportLabel_congr_proof {n k : ℕ} (hk : 1 ≤ k)
    (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1)) (X : SignedSubset n)
    (hlarge₁ hlarge₂ : 2 * k - 1 ≤ X.card) :
    matousekLargeSupportLabel hk hn C X hlarge₁ =
      matousekLargeSupportLabel hk hn C X hlarge₂ := by
  apply SignedLabel.ext
  · exact matousekLargeSupportPositive_congr_proof C X hlarge₁ hlarge₂
  · apply Fin.ext
    simp [matousekLargeSupportLabel, matousekLargeSupportIndex,
      matousekLargeSupportColor_congr_proof C X hlarge₁ hlarge₂]

theorem matousekLargeSupportLabel_antipode {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1))
    (hC : ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b)
    (X : SignedSubset n) (hlarge : 2 * k - 1 ≤ X.card) :
    matousekLargeSupportLabel hk hn C X.antipode
        (by simpa [SignedSubset.card_antipode] using hlarge) =
      (matousekLargeSupportLabel hk hn C X hlarge).neg := by
  change SignedLabel.mk
      (matousekLargeSupportPositive C X.antipode
        (by simpa [SignedSubset.card_antipode] using hlarge))
      (matousekLargeSupportIndex hk hn
        (matousekLargeSupportColor C X.antipode
          (by simpa [SignedSubset.card_antipode] using hlarge))) =
    SignedLabel.mk (!(matousekLargeSupportPositive C X hlarge))
      (matousekLargeSupportIndex hk hn (matousekLargeSupportColor C X hlarge))
  have hpositive :
      matousekLargeSupportPositive C X.antipode
          (by simpa [SignedSubset.card_antipode] using hlarge) =
        !(matousekLargeSupportPositive C X hlarge) :=
    matousekLargeSupportPositive_antipode hk C hC X hlarge
  have hindex :
      matousekLargeSupportIndex hk hn
          (matousekLargeSupportColor C X.antipode
            (by simpa [SignedSubset.card_antipode] using hlarge)) =
        matousekLargeSupportIndex hk hn (matousekLargeSupportColor C X hlarge) := by
    rw [matousekLargeSupportColor_antipode hk C hC X hlarge]
  exact SignedLabel.ext hpositive hindex

theorem matousekLargeSupportLabel_ne_neg_of_le {n k : ℕ} (hk : 1 ≤ k)
    (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1))
    (hC : ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b)
    {X Y : SignedSubset n}
    (hXlarge : 2 * k - 1 ≤ X.card) (hYlarge : 2 * k - 1 ≤ Y.card)
    (hXY : SignedSubset.Le X Y) :
    matousekLargeSupportLabel hk hn C X hXlarge ≠
      (matousekLargeSupportLabel hk hn C Y hYlarge).neg := by
  intro hcomp
  have hpositive :
      matousekLargeSupportPositive C X hXlarge =
        !(matousekLargeSupportPositive C Y hYlarge) := by
    have := congrArg SignedLabel.positive hcomp
    simpa [matousekLargeSupportLabel, SignedLabel.neg] using this
  have hindex :
      matousekLargeSupportIndex hk hn (matousekLargeSupportColor C X hXlarge) =
        matousekLargeSupportIndex hk hn (matousekLargeSupportColor C Y hYlarge) := by
    have := congrArg SignedLabel.index hcomp
    simpa [matousekLargeSupportLabel, SignedLabel.neg] using this
  have hcolor : matousekLargeSupportColor C X hXlarge =
      matousekLargeSupportColor C Y hYlarge := by
    apply Fin.ext
    have hindex_val := congrArg Fin.val hindex
    simp [matousekLargeSupportIndex] at hindex_val
    omega
  have hdisj :
      Disjoint
        (X.side (matousekLargeSupportPositive C X hXlarge))
        (Y.side (matousekLargeSupportPositive C Y hYlarge)) := by
    cases hYpos : matousekLargeSupportPositive C Y hYlarge
    · have hXpos : matousekLargeSupportPositive C X hXlarge = true := by
        simpa [hYpos] using hpositive
      simpa [hXpos, hYpos] using SignedSubset.side_disjoint_of_le_not hXY true
    · have hXpos : matousekLargeSupportPositive C X hXlarge = false := by
        simpa [hYpos] using hpositive
      simpa [hXpos, hYpos] using SignedSubset.side_disjoint_of_le_not hXY false
  have hmin_ne :
      minColorInSupport C
          (X.side (matousekLargeSupportPositive C X hXlarge))
          (matousekLargeSupportPositive_card C X hXlarge) ≠
        minColorInSupport C
          (Y.side (matousekLargeSupportPositive C Y hYlarge))
          (matousekLargeSupportPositive_card C Y hYlarge) :=
    minColorInSupport_ne_of_disjoint hk C hC hdisj
      (matousekLargeSupportPositive_card C X hXlarge)
      (matousekLargeSupportPositive_card C Y hYlarge)
  exact hmin_ne (by simpa [matousekLargeSupportColor] using hcolor)

theorem matousekSmallSupportLabel_ne_neg_large {n k : ℕ} (hk : 1 ≤ k)
    (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1))
    {X Y : SignedSubset n}
    (hX : X.Nonzero) (hXsmall : X.card ≤ 2 * k - 2)
    (hYlarge : 2 * k - 1 ≤ Y.card) :
    matousekSmallSupportLabel hk hn X hX hXsmall ≠
      (matousekLargeSupportLabel hk hn C Y hYlarge).neg := by
  intro hcomp
  have hindex :
      matousekSmallSupportIndex hk hn X hX hXsmall =
        matousekLargeSupportIndex hk hn (matousekLargeSupportColor C Y hYlarge) := by
    have := congrArg SignedLabel.index hcomp
    simpa [matousekSmallSupportLabel, matousekLargeSupportLabel, SignedLabel.neg] using this
  have hindex_val := congrArg Fin.val hindex
  have hXpos : 0 < X.card := SignedSubset.card_pos_of_nonzero hX
  have hcolor := (matousekLargeSupportColor C Y hYlarge).isLt
  simp [matousekSmallSupportIndex, matousekLargeSupportIndex] at hindex_val
  omega

theorem matousekLargeSupportLabel_ne_neg_small {n k : ℕ} (hk : 1 ≤ k)
    (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1))
    {X Y : SignedSubset n}
    (hXlarge : 2 * k - 1 ≤ X.card)
    (hY : Y.Nonzero) (hYsmall : Y.card ≤ 2 * k - 2) :
    matousekLargeSupportLabel hk hn C X hXlarge ≠
      (matousekSmallSupportLabel hk hn Y hY hYsmall).neg := by
  intro hcomp
  have hindex :
      matousekLargeSupportIndex hk hn (matousekLargeSupportColor C X hXlarge) =
        matousekSmallSupportIndex hk hn Y hY hYsmall := by
    have := congrArg SignedLabel.index hcomp
    simpa [matousekSmallSupportLabel, matousekLargeSupportLabel, SignedLabel.neg] using this
  have hindex_val := congrArg Fin.val hindex
  have hYpos : 0 < Y.card := SignedSubset.card_pos_of_nonzero hY
  have hcolor := (matousekLargeSupportColor C X hXlarge).isLt
  simp [matousekSmallSupportIndex, matousekLargeSupportIndex] at hindex_val
  omega





theorem matousekTuckerLabel_antipode {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1))
    (hC : ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b)
    (X : NonzeroSignedSubset n) :
    matousekTuckerLabel hk hn C X.antipode = (matousekTuckerLabel hk hn C X).neg := by
  unfold matousekTuckerLabel
  by_cases hsmall : X.1.card ≤ 2 * k - 2
  · have hsmall_ant : X.antipode.1.card ≤ 2 * k - 2 := by
      simpa [NonzeroSignedSubset.antipode, SignedSubset.card_antipode] using hsmall
    rw [dif_pos hsmall, dif_pos hsmall_ant]
    simpa [NonzeroSignedSubset.antipode,
      matousekSmallSupportLabel_congr_proof hk hn X.1.antipode] using
      matousekSmallSupportLabel_antipode hk hn X.1 X.2 hsmall
  · have hlarge : 2 * k - 1 ≤ X.1.card := by omega
    have hsmall_ant : ¬ X.antipode.1.card ≤ 2 * k - 2 := by
      simpa [NonzeroSignedSubset.antipode, SignedSubset.card_antipode] using hsmall
    rw [dif_neg hsmall, dif_neg hsmall_ant]
    simpa [NonzeroSignedSubset.antipode,
      matousekLargeSupportLabel_congr_proof hk hn C X.1,
      matousekLargeSupportLabel_congr_proof hk hn C X.1.antipode] using
      matousekLargeSupportLabel_antipode hk hn C hC X.1 hlarge

theorem matousekTuckerLabel_no_complementary {n k : ℕ} (hk : 1 ≤ k)
    (hn : 2 * k ≤ n)
    (C : KneserVertex n k → Fin (n - 2 * k + 1))
    (hC : ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b)
    (X Y : NonzeroSignedSubset n) :
    SignedSubset.Le X.1 Y.1 →
      matousekTuckerLabel hk hn C X ≠ (matousekTuckerLabel hk hn C Y).neg := by
  intro hXY
  unfold matousekTuckerLabel
  by_cases hXsmall : X.1.card ≤ 2 * k - 2
  · by_cases hYsmall : Y.1.card ≤ 2 * k - 2
    · simpa [hXsmall, hYsmall] using
        matousekSmallSupportLabel_ne_neg_of_le hk hn X.2 Y.2 hXsmall hYsmall hXY
    · have hYlarge : 2 * k - 1 ≤ Y.1.card := by omega
      simpa [hXsmall, hYsmall, matousekLargeSupportLabel_congr_proof hk hn C Y.1] using
        matousekSmallSupportLabel_ne_neg_large hk hn C X.2 hXsmall hYlarge
  · have hXlarge : 2 * k - 1 ≤ X.1.card := by omega
    by_cases hYsmall : Y.1.card ≤ 2 * k - 2
    · simpa [hXsmall, hYsmall, matousekLargeSupportLabel_congr_proof hk hn C X.1] using
        matousekLargeSupportLabel_ne_neg_small hk hn C hXlarge Y.2 hYsmall
    · have hYlarge : 2 * k - 1 ≤ Y.1.card := by omega
      simpa [hXsmall, hYsmall, matousekLargeSupportLabel_congr_proof hk hn C X.1,
        matousekLargeSupportLabel_congr_proof hk hn C Y.1] using
        matousekLargeSupportLabel_ne_neg_of_le hk hn C hC hXlarge hYlarge hXY

























namespace SignedPermutation



























theorem prefixChain_le {n : ℕ} (P : SignedPermutation n) {i j : Fin n} (hij : i ≤ j) :
    SignedSubset.Le (P.prefixChain i).1 (P.prefixChain j).1 := by
  constructor
  · intro x hx
    simp [prefixChain, prefixSignedSubset, prefixPos] at hx ⊢
    exact ⟨hx.1.trans hij, hx.2⟩
  · intro x hx
    simp [prefixChain, prefixSignedSubset, prefixNeg] at hx ⊢
    exact ⟨hx.1.trans hij, hx.2⟩



end SignedPermutation







theorem label_prefixChain_antipode {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (P : SignedPermutation n) (i : Fin n) :
    label (P.antipode.prefixChain i) = (label (P.prefixChain i)).neg := by
  rw [SignedPermutation.prefixChain_antipode]
  exact hantipodal (P.prefixChain i)

theorem prefix_strictMono_antipode_iff {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (P : SignedPermutation n) :
    (StrictMono fun i => (label (P.antipode.prefixChain i)).index) ↔
      StrictMono fun i => (label (P.prefixChain i)).index := by
  simp [label_prefixChain_antipode label hantipodal P, SignedLabel.neg]







theorem positiveAlternatingPrefixLabels_antipode_iff {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (P : SignedPermutation n) :
    PositiveAlternatingPrefixLabels label P.antipode ↔
      NegativeAlternatingPrefixLabels label P := by
  constructor
  · intro h
    refine ⟨(prefix_strictMono_antipode_iff label hantipodal P).mp h.1, ?_⟩
    intro i
    have hsign := h.2 i
    rw [label_prefixChain_antipode label hantipodal P i] at hsign
    simpa [NegativeAlternatingPrefixLabels, PositiveAlternatingPrefixLabels, SignedLabel.neg]
      using hsign
  · intro h
    refine ⟨(prefix_strictMono_antipode_iff label hantipodal P).mpr h.1, ?_⟩
    intro i
    have hsign := h.2 i
    rw [label_prefixChain_antipode label hantipodal P i]
    simp [SignedLabel.neg, hsign]

theorem positive_negative_alternating_disjoint {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset n → SignedLabel m) (P : SignedPermutation n) :
    PositiveAlternatingPrefixLabels label P →
      NegativeAlternatingPrefixLabels label P → False := by
  intro hpos hneg
  let i : Fin n := ⟨0, hn⟩
  have hp := hpos.2 i
  have hn' := hneg.2 i
  simp [i] at hp hn'
  rw [hp] at hn'
  simp at hn'





theorem positiveAlternatingPrefixLabelChains_card_eq_negative {n m : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    (positiveAlternatingPrefixLabelChains label).card =
      (negativeAlternatingPrefixLabelChains label).card := by
  classical
  refine Finset.card_bij (fun P _ => SignedPermutation.antipode P) ?mem ?inj ?surj
  · intro P hP
    have hpos : PositiveAlternatingPrefixLabels label P := by
      simpa [positiveAlternatingPrefixLabelChains] using hP
    have hneg : NegativeAlternatingPrefixLabels label P.antipode := by
      have hiff := positiveAlternatingPrefixLabels_antipode_iff label hantipodal P.antipode
      have hpos' : PositiveAlternatingPrefixLabels label P.antipode.antipode := by
        simpa [SignedPermutation.antipode_involutive P] using hpos
      exact hiff.mp hpos'
    simpa [negativeAlternatingPrefixLabelChains] using hneg
  · intro P hP Q hQ hPQ
    have h := congrArg SignedPermutation.antipode hPQ
    simpa [SignedPermutation.antipode_involutive P, SignedPermutation.antipode_involutive Q] using h
  · intro Q hQ
    have hneg : NegativeAlternatingPrefixLabels label Q := by
      simpa [negativeAlternatingPrefixLabelChains] using hQ
    refine ⟨Q.antipode, ?_, ?_⟩
    · have hpos : PositiveAlternatingPrefixLabels label Q.antipode := by
        exact (positiveAlternatingPrefixLabels_antipode_iff label hantipodal Q).mpr hneg
      simpa [positiveAlternatingPrefixLabelChains] using hpos
    · exact SignedPermutation.antipode_involutive Q

theorem positive_negativeAlternatingPrefixLabelChains_disjoint {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset n → SignedLabel m) :
    Disjoint (positiveAlternatingPrefixLabelChains label)
      (negativeAlternatingPrefixLabelChains label) := by
  classical
  rw [Finset.disjoint_left]
  intro P hpos hneg
  exact positive_negative_alternating_disjoint hn label P
    (by simpa [positiveAlternatingPrefixLabelChains] using hpos)
    (by simpa [negativeAlternatingPrefixLabelChains] using hneg)



theorem alternatingPrefixLabelChains_card {n m : ℕ} (hn : 0 < n)
    (label : NonzeroSignedSubset n → SignedLabel m)
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    (alternatingPrefixLabelChains label).card =
      2 * (positiveAlternatingPrefixLabelChains label).card := by
  classical
  rw [alternatingPrefixLabelChains,
    Finset.card_union_of_disjoint (positive_negativeAlternatingPrefixLabelChains_disjoint hn label),
    positiveAlternatingPrefixLabelChains_card_eq_negative label hantipodal]
  omega





















/-! ### Endpoint-count form of the remaining Ky Fan parity frontier -/



















namespace PathEndpointDecomposition



end PathEndpointDecomposition



















theorem tuckerLemmaStatement_one : TuckerLemmaStatement 1 := by
  intro label _
  let z : Fin 1 := ⟨0, by omega⟩
  let X : NonzeroSignedSubset 1 :=
    ⟨{ pos := {z}, neg := ∅, disjoint := by simp },
      by simp [SignedSubset.Nonzero]⟩
  exact Fin.elim0 (label X).index

















theorem kneserColoringProducesTuckerCounterexample_of_matousek (n k : ℕ)
    (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    KneserColoringProducesTuckerCounterexample n k := by
  intro C hC
  refine ⟨matousekTuckerLabel hk hn C, ?_, ?_⟩
  · intro X
    exact matousekTuckerLabel_antipode hk hn C hC X
  · intro X Y hXY
    exact matousekTuckerLabel_no_complementary hk hn C hC X Y hXY

/--
If Tucker's lemma and Matoušek's coloring-to-labeling bridge are available,
the hard Kneser lower bound follows immediately.
-/
theorem kneser_chromatic_lower_bound_from_tucker (n k : ℕ)
    (htucker : TuckerLemmaStatement n)
    (hbridge : KneserColoringProducesTuckerCounterexample n k) :
    ¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
      ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b := by
  rintro ⟨C, hC⟩
  obtain ⟨label, hantipodal, hno_complementary⟩ := hbridge C hC
  obtain ⟨X, Y, hXY, hcomp⟩ := htucker label hantipodal
  exact hno_complementary X Y hXY hcomp

theorem kneser_chromatic_lower_bound_from_tucker_matousek (n k : ℕ)
    (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (htucker : TuckerLemmaStatement n) :
    ¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
      ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b :=
  kneser_chromatic_lower_bound_from_tucker n k htucker
    (kneserColoringProducesTuckerCounterexample_of_matousek n k hk hn)













/--
Chapter 39 (Lovász's theorem on Kneser graph chromatic number, conditional on
the discrete Tucker lemma): the upper bound is explicit, and the lower bound
is derived from Tucker's lemma via the formalized Matoušek labeling above.

Remaining gap to an unconditional theorem in Mathlib: prove
`TuckerLemmaStatement`.
-/
theorem chapter39 {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (htucker : TuckerLemmaStatement n) :
    (∃ C : KneserVertex n k → Fin (n - 2 * k + 2),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) ∧
    (¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) := by
  refine ⟨?_, ?_⟩
  · exact kneser_chromatic_upper_bound n k hk hn
  · exact kneser_chromatic_lower_bound_from_tucker_matousek n k hk hn htucker











end ProofsInTheBook.Chapter39

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter39
import Mathlib.Data.Fin.Tuple.Sort
-/
/- Source module: ProofsInTheBook.Chapter39Tucker -/
section
set_option autoImplicit true


/-!
# Chapter 39 (Kneser) — Tucker lemma, sound foundation

A correct (non-degenerate) reduction for `TuckerLemmaStatement`, replacing the earlier
empty-alternating-chain framework (whose `PositiveAlternatingPrefixLabels` is provably
unsatisfiable: it demands `StrictMono (Fin n → Fin (n-1))`, impossible by pigeonhole).

The genuine combinatorial content: along any maximal chain (a signed-permutation prefix
chain of length `n`), the `n` labels live in `SignedLabel (n-1)` (only `n-1` indices), so two
of them share an index.  If two comparable signed subsets carry same-index, opposite-sign
labels, that *is* a complementary comparable pair — the Tucker conclusion.  So Tucker reduces
to producing one chain with a same-index, opposite-sign pair; the "same index" half is free
(pigeonhole), and the remaining content (forcing opposite signs via antipodality) is the real
path argument, now resting on a sound base.
-/

namespace ProofsInTheBook.Chapter39

open SignedPermutation





theorem tuckerLemmaStatement_of_chain_complementary_of_no_complementary {n : ℕ}
    (h : ∀ label : NonzeroSignedSubset n → SignedLabel (n - 1),
          (∀ X, label X.antipode = (label X).neg) →
          NoComplementaryComparableLabels label →
          ∃ (P : SignedPermutation n) (i j : Fin n), i < j ∧
            (label (P.prefixChain i)).index = (label (P.prefixChain j)).index ∧
            (label (P.prefixChain i)).positive ≠ (label (P.prefixChain j)).positive) :
    TuckerLemmaStatement n := by
  intro label hanti
  by_contra hnone
  have hno : NoComplementaryComparableLabels label := by
    intro X Y hXY hcomp
    exact hnone ⟨X, Y, hXY, hcomp⟩
  obtain ⟨P, i, j, hij, hidx, hsign⟩ := h label hanti hno
  have hcomp : label (P.prefixChain i) = (label (P.prefixChain j)).neg := by
    refine SignedLabel.ext ?_ ?_
    · simp only [SignedLabel.neg]
      revert hsign
      cases hpi : (label (P.prefixChain i)).positive <;>
        cases hpj : (label (P.prefixChain j)).positive <;> simp
    · simp only [SignedLabel.neg]
      exact hidx
  exact hno (P.prefixChain i) (P.prefixChain j)
    (prefixChain_le P (le_of_lt hij)) hcomp

/-! ## Hemisphere and equator model -/

































theorem equatorEmbed_le {r : ℕ} {X Y : NonzeroSignedSubset r}
    (hXY : SignedSubset.Le X.1 Y.1) :
    SignedSubset.Le (equatorEmbed X).1 (equatorEmbed Y).1 := by
  constructor
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨i, hXY.1 hi, rfl⟩
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨i, hXY.2 hi, rfl⟩

theorem signedSubsetEquatorEmbed_antipode {r : ℕ} (X : SignedSubset r) :
    signedSubsetEquatorEmbed X.antipode = (signedSubsetEquatorEmbed X).antipode := by
  apply signedSubset_ext_pos_neg
  · ext i
    simp [signedSubsetEquatorEmbed, SignedSubset.antipode]
  · ext i
    simp [signedSubsetEquatorEmbed, SignedSubset.antipode]

theorem equatorEmbed_antipode {r : ℕ} (X : NonzeroSignedSubset r) :
    equatorEmbed X.antipode = (equatorEmbed X).antipode := by
  apply Subtype.ext
  exact signedSubsetEquatorEmbed_antipode X.1





theorem equatorRestrictedLabelOf_antipodal {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    ∀ X, equatorRestrictedLabelOf label X.antipode =
      (equatorRestrictedLabelOf label X).neg := by
  intro X
  simpa [equatorRestrictedLabelOf, equatorEquiv, equatorEmbed_antipode] using
    hantipodal (equatorEmbed X)

theorem equatorRestrictedLabelOf_noComplementary {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hno : NoComplementaryComparableLabels label) :
    NoComplementaryComparableLabels (equatorRestrictedLabelOf label) := by
  intro X Y hXY hcomp
  have hcomp' : label (equatorEmbed X) = (label (equatorEmbed Y)).neg := by
    simpa [equatorRestrictedLabelOf, equatorEquiv] using hcomp
  exact hno (equatorEmbed X) (equatorEmbed Y) (equatorEmbed_le hXY) hcomp'

theorem equatorRestrictedLabel_antipodal {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    ∀ X, equatorRestrictedLabel label X.antipode =
      (equatorRestrictedLabel label X).neg := by
  intro X
  simpa [equatorRestrictedLabel, equatorEquiv, equatorEmbed_antipode] using
    hantipodal (equatorEmbed X)

theorem equatorRestrictedLabel_noComplementary {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (hno : NoComplementaryComparableLabels label) :
    NoComplementaryComparableLabels (equatorRestrictedLabel label) := by
  intro X Y hXY hcomp
  have hcomp' : label (equatorEmbed X) = (label (equatorEmbed Y)).neg := by
    simpa [equatorRestrictedLabel, equatorEquiv] using hcomp
  exact hno (equatorEmbed X) (equatorEmbed Y) (equatorEmbed_le hXY) hcomp'









/-! ## Label-set `A` ridges and the local sigma-degree count -/





@[simp]
theorem alternatingLabel_positive (k : Fin d) :
    (alternatingLabel k).positive = decide (Even k.val) := rfl

theorem alternatingLabel_inj {d : ℕ} {a b : Fin d} :
    alternatingLabel a = alternatingLabel b ↔ a = b := by
  constructor
  · intro h
    have hidx := congrArg SignedLabel.index h
    simpa [alternatingLabel] using hidx
  · intro h
    subst h
    rfl

theorem alternatingLabel_neg_ne {d : ℕ} (a b : Fin d) :
    (alternatingLabel a).neg ≠ alternatingLabel b := by
  intro h
  have hidx : a = b := by
    have hidx' := congrArg SignedLabel.index h
    simpa [alternatingLabel, SignedLabel.neg] using hidx'
  subst b
  have hpos := congrArg SignedLabel.positive h
  simp [alternatingLabel, SignedLabel.neg] at hpos

theorem signedLabel_eq_alternating_or_neg {d : ℕ} (L : SignedLabel d) :
    L = alternatingLabel L.index ∨ L = (alternatingLabel L.index).neg := by
  cases L with
  | mk positive index =>
      by_cases h : positive = decide (Even index.val)
      · left
        apply SignedLabel.ext
        · exact h
        · rfl
      · right
        apply SignedLabel.ext
        · cases positive <;> cases hidx : decide (Even index.val) <;>
            simp [hidx, SignedLabel.neg] at h ⊢
        · rfl



theorem alternatingLabelSetA_card (d : ℕ) :
    (alternatingLabelSetA d).card = d := by
  classical
  rw [alternatingLabelSetA, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact alternatingLabel_inj.mp h

/-! ### Alternating labels along an arbitrary increasing index set -/

















theorem alternatingNegLabelOf_inj {r m : ℕ} {idx : Fin r → Fin m}
    (hidx : Function.Injective idx) {a b : Fin r} :
    (alternatingLabelOf idx a).neg = (alternatingLabelOf idx b).neg ↔ a = b := by
  constructor
  · intro h
    apply hidx
    have hidx' := congrArg SignedLabel.index h
    simpa [alternatingLabelOf, SignedLabel.neg] using hidx'
  · intro h
    subst h
    rfl

theorem alternatingNegLabelSetOf_card {r m : ℕ} {idx : Fin r → Fin m}
    (hidx : Function.Injective idx) :
    (alternatingNegLabelSetOf idx).card = r := by
  classical
  rw [alternatingNegLabelSetOf, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact (alternatingNegLabelOf_inj hidx).mp h























/-! ### Pure sign-sequence deletion parity -/













theorem signSeq_not_bad_iff {k : ℕ} (s : Fin (k + 1) → Bool) (i : Fin (k + 1)) :
    ¬ signSeqBad s i ↔ s i = decide (Even i.val) := by
  unfold signSeqBad
  cases h : decide (Even i.val) <;> cases hs : s i <;> simp [h, hs]

theorem signSeq_bad_iff_not_altPos {k : ℕ} (s : Fin (k + 1) → Bool)
    (i : Fin (k + 1)) :
    signSeqBad s i ↔ ¬ s i = decide (Even i.val) := by
  unfold signSeqBad
  cases h : decide (Even i.val) <;> cases hs : s i <;> simp [h, hs]

theorem signSeqDoor_iff_bad_cut {k : ℕ} (s : Fin (k + 1) → Bool) (i : Fin (k + 1)) :
    signSeqDoor s i ↔
      (∀ j : Fin (k + 1), j < i → ¬ signSeqBad s j) ∧
        (∀ j : Fin (k + 1), i < j → signSeqBad s j) := by
  constructor
  · intro h
    constructor
    · intro j hji
      exact (signSeq_not_bad_iff s j).mpr (h.1 j hji)
    · intro j hij
      exact h.2 j hij
  · intro h
    constructor
    · intro j hji
      exact (signSeq_not_bad_iff s j).mp (h.1 j hji)
    · intro j hij
      exact h.2 j hij

theorem signSeq_not_even_succ_decide (a : ℕ) :
    (!decide (Even (a + 1))) = decide (Even a) := by
  by_cases ha : Even a <;> simp [ha, Nat.even_add_one]



theorem signSeqDoor_iff_remove_altPos {k : ℕ} (s : Fin (k + 1) → Bool)
    (i : Fin (k + 1)) :
    signSeqDoor s i ↔ signSeqAltPos (fun a : Fin k => s (i.succAbove a)) := by
  constructor
  · intro h a
    by_cases hlt : i.succAbove a < i
    · have hs := h.1 (i.succAbove a) hlt
      have hcastlt : Fin.castSucc a < i :=
        (Fin.succAbove_lt_iff_castSucc_lt i a).mp hlt
      have hsa := Fin.succAbove_of_castSucc_lt i a hcastlt
      have hval : (i.succAbove a).val = a.val := by
        rw [hsa]
        rfl
      simpa [hval] using hs
    · have hgt : i < i.succAbove a := by
        have hne : i ≠ i.succAbove a := Fin.ne_succAbove i a
        exact lt_of_le_of_ne (le_of_not_gt hlt) hne
      have hs := h.2 (i.succAbove a) hgt
      have hlecast : i ≤ Fin.castSucc a :=
        (Fin.lt_succAbove_iff_le_castSucc i a).mp hgt
      have hsa := Fin.succAbove_of_le_castSucc i a hlecast
      have hval : (i.succAbove a).val = a.val + 1 := by
        rw [hsa]
        rfl
      change s (i.succAbove a) = decide (Even a.val)
      rw [hs, hval]
      exact signSeq_not_even_succ_decide a.val
  · intro h
    constructor
    · intro j hji
      have hne : j ≠ i := ne_of_lt hji
      rcases Fin.exists_succAbove_eq hne with ⟨a, ha⟩
      have hdel := h a
      have hsa_lt : i.succAbove a < i := by
        simpa [ha] using hji
      have hcastlt : Fin.castSucc a < i :=
        (Fin.succAbove_lt_iff_castSucc_lt i a).mp hsa_lt
      have hsa := Fin.succAbove_of_castSucc_lt i a hcastlt
      have hval : a.val = j.val := by
        have hv := congrArg Fin.val (hsa.symm.trans ha)
        simpa using hv
      have hs_j : s j = decide (Even a.val) := by
        simpa [ha] using hdel
      simpa [hval] using hs_j
    · intro j hij
      have hne : j ≠ i := ne_of_gt hij
      rcases Fin.exists_succAbove_eq hne with ⟨a, ha⟩
      have hdel := h a
      have hsa_gt : i < i.succAbove a := by
        simpa [ha] using hij
      have hlecast : i ≤ Fin.castSucc a :=
        (Fin.lt_succAbove_iff_le_castSucc i a).mp hsa_gt
      have hsa := Fin.succAbove_of_le_castSucc i a hlecast
      have hval : j.val = a.val + 1 := by
        have hv := congrArg Fin.val (hsa.symm.trans ha)
        simpa using hv.symm
      have hs_j : s j = decide (Even a.val) := by
        simpa [ha] using hdel
      rw [hs_j, hval]
      exact (signSeq_not_even_succ_decide a.val).symm

theorem signSeqDoor_nonadjacent_false {k : ℕ} {s : Fin (k + 1) → Bool}
    {i j : Fin (k + 1)} (hi : signSeqDoor s i) (hj : signSeqDoor s j)
    (_hij : i < j) :
    j.val ≤ i.val + 1 := by
  by_contra hle
  have hlt : i.val + 1 < j.val := by omega
  let t : Fin (k + 1) := ⟨i.val + 1, by omega⟩
  have hit : i < t := by
    exact Fin.lt_iff_val_lt_val.mpr (by simp [t])
  have htj : t < j := by
    exact Fin.lt_iff_val_lt_val.mpr (by simpa [t] using hlt)
  have hbad : signSeqBad s t := (signSeqDoor_iff_bad_cut s i).mp hi |>.2 t hit
  have hnot : ¬ signSeqBad s t := (signSeqDoor_iff_bad_cut s j).mp hj |>.1 t htj
  exact hnot hbad

theorem signSeqDoorSet_card_le_two {k : ℕ} (s : Fin (k + 1) → Bool) :
    (signSeqDoorSet s).card ≤ 2 := by
  classical
  by_contra hle
  have htwo : 2 < (signSeqDoorSet s).card := by omega
  rcases Finset.two_lt_card.mp htwo with
    ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩
  have hdoor_a : signSeqDoor s a := by simpa [signSeqDoorSet] using ha
  have hdoor_b : signSeqDoor s b := by simpa [signSeqDoorSet] using hb
  have hdoor_c : signSeqDoor s c := by simpa [signSeqDoorSet] using hc
  have hcontr_pair :
      ∀ {x y : Fin (k + 1)}, signSeqDoor s x → signSeqDoor s y → x < y →
        x.val + 1 < y.val → False := by
    intro x y hx hy hxy hgap
    have hle' := signSeqDoor_nonadjacent_false hx hy hxy
    omega
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · rcases lt_trichotomy c a with hca | hcaeq | haclt
    · exact hcontr_pair hdoor_c hdoor_b (lt_trans hca hablt) (by
        have h1 := Fin.lt_iff_val_lt_val.mp hca
        have h2 := Fin.lt_iff_val_lt_val.mp hablt
        omega)
    · exact hac hcaeq.symm
    · rcases lt_trichotomy c b with hcb | hcbeq | hbclt
      · exact hcontr_pair hdoor_a hdoor_b hablt (by
          have h1 := Fin.lt_iff_val_lt_val.mp haclt
          have h2 := Fin.lt_iff_val_lt_val.mp hcb
          omega)
      · exact hbc hcbeq.symm
      · exact hcontr_pair hdoor_a hdoor_c (lt_trans hablt hbclt) (by
          have h1 := Fin.lt_iff_val_lt_val.mp hablt
          have h2 := Fin.lt_iff_val_lt_val.mp hbclt
          omega)
  · rcases lt_trichotomy c b with hcb | hcbeq | hbclt
    · exact hcontr_pair hdoor_c hdoor_a (lt_trans hcb hbalt) (by
        have h1 := Fin.lt_iff_val_lt_val.mp hcb
        have h2 := Fin.lt_iff_val_lt_val.mp hbalt
        omega)
    · exact hbc hcbeq.symm
    · rcases lt_trichotomy c a with hca | hcaeq | haclt
      · exact hcontr_pair hdoor_b hdoor_a hbalt (by
          have h1 := Fin.lt_iff_val_lt_val.mp hbclt
          have h2 := Fin.lt_iff_val_lt_val.mp hca
          omega)
      · exact hac hcaeq.symm
      · exact hcontr_pair hdoor_b hdoor_c (lt_trans hbalt haclt) (by
          have h1 := Fin.lt_iff_val_lt_val.mp hbalt
          have h2 := Fin.lt_iff_val_lt_val.mp haclt
          omega)

theorem signSeqDoor_next_of_not_bad {k : ℕ} {s : Fin (k + 1) → Bool}
    {i : Fin (k + 1)} (hi : signSeqDoor s i)
    (hnot : ¬ signSeqBad s i) (hik : i.val < k) :
    signSeqDoor s ⟨i.val + 1, by omega⟩ := by
  rw [signSeqDoor_iff_bad_cut] at hi ⊢
  constructor
  · intro j hj
    have hjv : j.val < i.val + 1 := Fin.lt_iff_val_lt_val.mp hj
    by_cases hji : j < i
    · exact hi.1 j hji
    · have hji_eq : j = i := by
        apply Fin.ext
        have hle : i.val ≤ j.val := by
          exact le_of_not_gt (by
            intro hv
            exact hji (Fin.lt_iff_val_lt_val.mpr hv))
        omega
      simpa [hji_eq] using hnot
  · intro j hj
    apply hi.2
    exact Fin.lt_iff_val_lt_val.mpr (by
      have hjv : i.val + 1 < j.val := Fin.lt_iff_val_lt_val.mp hj
      omega)

theorem signSeqDoor_prev_of_bad {k : ℕ} {s : Fin (k + 1) → Bool}
    {i : Fin (k + 1)} (hi : signSeqDoor s i)
    (hbad : signSeqBad s i) (hi0 : 0 < i.val) :
    signSeqDoor s ⟨i.val - 1, by omega⟩ := by
  rw [signSeqDoor_iff_bad_cut] at hi ⊢
  constructor
  · intro j hj
    apply hi.1
    exact Fin.lt_iff_val_lt_val.mpr (by
      have hjv : j.val < i.val - 1 := Fin.lt_iff_val_lt_val.mp hj
      omega)
  · intro j hj
    have hjv : i.val - 1 < j.val := Fin.lt_iff_val_lt_val.mp hj
    by_cases hij : i < j
    · exact hi.2 j hij
    · have hji_eq : j = i := by
        apply Fin.ext
        have hle : j.val ≤ i.val := by
          exact le_of_not_gt (by
            intro hv
            exact hij (Fin.lt_iff_val_lt_val.mpr hv))
        omega
      simpa [hji_eq] using hbad

theorem signSeqDoorSet_eq_singleton_last_of_altPos {k : ℕ}
    {s : Fin (k + 1) → Bool} (hpos : signSeqAltPos s) :
    signSeqDoorSet s = {Fin.last k} := by
  classical
  ext i
  constructor
  · intro hi
    have hdoor : signSeqDoor s i := by simpa [signSeqDoorSet] using hi
    by_cases hilast : i = Fin.last k
    · simp [hilast]
    · have hlt : i < Fin.last k := Fin.lt_last_iff_ne_last.mpr hilast
      have hsuf := hdoor.2 (Fin.last k) hlt
      have hposlast := hpos (Fin.last k)
      have hbad : decide (Even (Fin.last k).val) = !decide (Even (Fin.last k).val) :=
        hposlast.symm.trans hsuf
      cases decide (Even (Fin.last k).val) <;> simp at hbad
  · intro hi
    simp only [Finset.mem_singleton] at hi
    subst i
    have hdoor : signSeqDoor s (Fin.last k) := by
      constructor
      · intro j _hj
        exact hpos j
      · intro j hj
        exact False.elim ((not_lt_of_ge (Fin.le_last j)) hj)
    simpa [signSeqDoorSet] using hdoor

theorem signSeqDoorSet_eq_singleton_zero_of_altNeg {k : ℕ}
    {s : Fin (k + 1) → Bool} (hneg : signSeqAltNeg s) :
    signSeqDoorSet s = {0} := by
  classical
  ext i
  constructor
  · intro hi
    have hdoor : signSeqDoor s i := by simpa [signSeqDoorSet] using hi
    by_cases hi0 : i = 0
    · simp [hi0]
    · have hlt : (0 : Fin (k + 1)) < i := Fin.pos_iff_ne_zero.mpr hi0
      have hpref := hdoor.1 0 hlt
      have hneg0 := hneg 0
      have hbad : decide (Even (0 : Fin (k + 1)).val) =
          !decide (Even (0 : Fin (k + 1)).val) :=
        hpref.symm.trans hneg0
      cases decide (Even (0 : Fin (k + 1)).val) <;> simp at hbad
  · intro hi
    simp only [Finset.mem_singleton] at hi
    subst i
    have hdoor : signSeqDoor s (0 : Fin (k + 1)) := by
      constructor
      · intro j hj
        exact False.elim ((not_lt_of_ge (Fin.zero_le j)) hj)
      · intro j _hj
        exact hneg j
    simpa [signSeqDoorSet] using hdoor



theorem signSeqDeletionParity {k : ℕ} (s : Fin (k + 1) → Bool) :
    Odd (signSeqDoorSet s).card ↔ signSeqAltPos s ∨ signSeqAltNeg s := by
  classical
  constructor
  · intro hodd
    have hle := signSeqDoorSet_card_le_two s
    have hcard : (signSeqDoorSet s).card = 1 := by
      rcases hodd with ⟨a, ha⟩
      omega
    have hposcard : 0 < (signSeqDoorSet s).card := by omega
    obtain ⟨i, hi_mem⟩ := Finset.card_pos.mp hposcard
    have hi : signSeqDoor s i := by simpa [signSeqDoorSet] using hi_mem
    by_cases hk0 : k = 0
    · subst k
      fin_cases i
      by_cases hs0 : s 0 = true
      · left
        intro j
        fin_cases j
        simpa [hs0]
      · right
        have hsfalse : s 0 = false := by
          cases h : s 0 <;> simp [h] at hs0 ⊢
        intro j
        fin_cases j
        simpa [hsfalse]
    · have hend : i = 0 ∨ i = Fin.last k := by
        by_contra hend
        push_neg at hend
        have hi0v : 0 < i.val := Fin.pos_iff_ne_zero.mpr hend.1
        have hikv : i.val < k := by
          have hilast : i ≠ Fin.last k := hend.2
          have hlelast : i ≤ Fin.last k := Fin.le_last i
          have hneval : i.val ≠ k := by
            intro hv
            exact hilast (Fin.ext (by simpa [Fin.last] using hv))
          have hleval : i.val ≤ k := by simpa [Fin.last] using hlelast
          omega
        by_cases hbad : signSeqBad s i
        · let p : Fin (k + 1) := ⟨i.val - 1, by omega⟩
          have hp : signSeqDoor s p := signSeqDoor_prev_of_bad hi hbad hi0v
          have hp_mem : p ∈ signSeqDoorSet s := by simpa [signSeqDoorSet] using hp
          have hp_ne : p ≠ i := by
            intro hpi
            have hv := congrArg Fin.val hpi
            dsimp [p] at hv
            omega
          have htwo : 1 < (signSeqDoorSet s).card :=
            Finset.one_lt_card.mpr ⟨p, hp_mem, i, hi_mem, hp_ne⟩
          omega
        · let q : Fin (k + 1) := ⟨i.val + 1, by omega⟩
          have hq : signSeqDoor s q := signSeqDoor_next_of_not_bad hi hbad hikv
          have hq_mem : q ∈ signSeqDoorSet s := by simpa [signSeqDoorSet] using hq
          have hq_ne : q ≠ i := by
            intro hqi
            have hv := congrArg Fin.val hqi
            dsimp [q] at hv
            omega
          have htwo : 1 < (signSeqDoorSet s).card :=
            Finset.one_lt_card.mpr ⟨q, hq_mem, i, hi_mem, hq_ne⟩
          omega
      rcases hend with hi0 | hilast
      · right
        intro j
        subst i
        by_cases hj0 : j = 0
        · subst j
          by_contra hnot
          let q : Fin (k + 1) := ⟨1, by omega⟩
          have hnext : signSeqDoor s q := by
            have hkpos : 0 < k := by omega
            have hzero : (0 : Fin (k + 1)).val < k := by simpa using hkpos
            exact signSeqDoor_next_of_not_bad hi
              (by
                intro hb
                exact hnot hb) hzero
          have hnext_mem : q ∈ signSeqDoorSet s := by
            simpa [signSeqDoorSet] using hnext
          have hne : q ≠ 0 := by
            intro h
            have hv := congrArg Fin.val h
            dsimp [q] at hv
            omega
          have htwo : 1 < (signSeqDoorSet s).card :=
            Finset.one_lt_card.mpr ⟨q, hnext_mem, 0, hi_mem, hne⟩
          omega
        · have hlt : (0 : Fin (k + 1)) < j := Fin.pos_iff_ne_zero.mpr hj0
          exact hi.2 j hlt
      · left
        intro j
        subst i
        by_cases hjlast : j = Fin.last k
        · subst j
          by_contra hnot
          let p : Fin (k + 1) := ⟨k - 1, by omega⟩
          have hprev : signSeqDoor s p := by
            exact signSeqDoor_prev_of_bad hi
              ((signSeq_bad_iff_not_altPos s (Fin.last k)).mpr hnot)
              (by simp [Fin.last]; omega)
          have hprev_mem : p ∈ signSeqDoorSet s := by
            simpa [signSeqDoorSet] using hprev
          have hne : p ≠ Fin.last k := by
            intro h
            have hv := congrArg Fin.val h
            dsimp [p] at hv
            simp [Fin.last] at hv
            omega
          have htwo : 1 < (signSeqDoorSet s).card :=
            Finset.one_lt_card.mpr ⟨p, hprev_mem, Fin.last k, hi_mem, hne⟩
          omega
        · have hlt : j < Fin.last k := Fin.lt_last_iff_ne_last.mpr hjlast
          exact hi.1 j hlt
  · intro h
    rcases h with hpos | hneg
    · rw [signSeqDoorSet_eq_singleton_last_of_altPos hpos]
      simp
    · rw [signSeqDoorSet_eq_singleton_zero_of_altNeg hneg]
      simp

/-! ### Sorted label-sequence deletion parity -/











theorem sortedLabelSeq_isAltPos_iff_signSeqAltPos {k m : ℕ}
    {idx : Fin k → Fin m} (hidx : StrictMono idx)
    {sgn : Fin k → Bool} {L : Fin k → SignedLabel m}
    (hL : ∀ a : Fin k, L a = { positive := sgn a, index := idx a }) :
    IsAltPosLabelSeq L ↔ signSeqAltPos sgn := by
  classical
  constructor
  · rintro ⟨eta, heta, hset⟩
    have hrange : Set.range idx = Set.range eta := by
      ext x
      constructor
      · rintro ⟨a, rfl⟩
        have hmem : L a ∈ alternatingLabelSetOf eta := by
          rw [← hset]
          simp [labelSeqSet]
        rcases Finset.mem_image.mp hmem with ⟨b, _hb, hb⟩
        exact ⟨b, by
          have hidxeq := congrArg SignedLabel.index hb
          simpa [hL a, alternatingLabelOf] using hidxeq⟩
      · rintro ⟨b, rfl⟩
        have hmem : alternatingLabelOf eta b ∈ labelSeqSet L := by
          rw [hset]
          simp [alternatingLabelSetOf]
        rcases Finset.mem_image.mp hmem with ⟨a, _ha, ha⟩
        exact ⟨a, by
          have hidxeq := congrArg SignedLabel.index ha
          simpa [hL a, alternatingLabelOf] using hidxeq⟩
    have heta_eq : idx = eta := (StrictMono.range_inj hidx heta).mp hrange
    subst eta
    intro a
    have hmem : L a ∈ alternatingLabelSetOf idx := by
      rw [← hset]
      simp [labelSeqSet]
    rcases Finset.mem_image.mp hmem with ⟨b, _hb, hb⟩
    have hba : b = a := by
      apply hidx.injective
      have hidxeq := congrArg SignedLabel.index hb
      simpa [hL a, alternatingLabelOf] using hidxeq
    have hpos := congrArg SignedLabel.positive hb
    subst b
    simpa [hL a, alternatingLabelOf] using hpos.symm
  · intro hsgn
    refine ⟨idx, hidx, ?_⟩
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
      refine Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ?_⟩
      rw [← ha, hL a]
      apply SignedLabel.ext
      · simp [alternatingLabelOf, hsgn a]
      · simp [alternatingLabelOf]
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
      refine Finset.mem_image.mpr ⟨a, Finset.mem_univ a, ?_⟩
      rw [← ha, hL a]
      apply SignedLabel.ext
      · simp [alternatingLabelOf, hsgn a]
      · simp [alternatingLabelOf]





theorem sortedLabelSeq_deletion_iff_signSeqDoor {k m : ℕ}
    {idx : Fin (k + 1) → Fin m} (hidx : StrictMono idx)
    {sgn : Fin (k + 1) → Bool} {L : Fin (k + 1) → SignedLabel m}
    (hL : ∀ a : Fin (k + 1), L a = { positive := sgn a, index := idx a })
    (j : Fin (k + 1)) :
    IsAltPosLabelSeq (fun a : Fin k => L (j.succAbove a)) ↔ signSeqDoor sgn j := by
  have hidx_del : StrictMono fun a : Fin k => idx (j.succAbove a) :=
    hidx.comp (Fin.strictMono_succAbove j)
  have hL_del :
      ∀ a : Fin k,
        (fun a : Fin k => L (j.succAbove a)) a =
          { positive := (fun a : Fin k => sgn (j.succAbove a)) a,
            index := (fun a : Fin k => idx (j.succAbove a)) a } := by
    intro a
    exact hL (j.succAbove a)
  exact (sortedLabelSeq_isAltPos_iff_signSeqAltPos hidx_del hL_del).trans
    (signSeqDoor_iff_remove_altPos sgn j).symm

theorem sortedLabelSeq_deletionParity {k m : ℕ}
    {idx : Fin (k + 1) → Fin m} (hidx : StrictMono idx)
    {sgn : Fin (k + 1) → Bool} {L : Fin (k + 1) → SignedLabel m}
    (hL : ∀ a : Fin (k + 1), L a = { positive := sgn a, index := idx a }) :
    Odd (labelSeqAltPosDeletionSet L).card ↔
      IsAltPosLabelSeq L ∨ IsAltNegLabelSeq L := by
  classical
  have hset : labelSeqAltPosDeletionSet L = signSeqDoorSet sgn := by
    ext j
    simp [labelSeqAltPosDeletionSet, signSeqDoorSet,
      sortedLabelSeq_deletion_iff_signSeqDoor hidx hL j]
  rw [hset, signSeqDeletionParity]
  constructor
  · intro h
    rcases h with hpos | hneg
    · left
      exact (sortedLabelSeq_isAltPos_iff_signSeqAltPos hidx hL).mpr hpos
    · right
      exact (sortedLabelSeq_isAltNeg_iff_signSeqAltNeg hidx hL).mpr hneg
  · intro h
    rcases h with hpos | hneg
    · left
      exact (sortedLabelSeq_isAltPos_iff_signSeqAltPos hidx hL).mp hpos
    · right
      exact (sortedLabelSeq_isAltNeg_iff_signSeqAltNeg hidx hL).mp hneg

theorem IsAltPos_iff_labelSeq {k m n : ℕ}
    {label : NonzeroSignedSubset n → SignedLabel m}
    {sigma : Fin k → NonzeroSignedSubset n} :
    IsAltPos label sigma ↔ IsAltPosLabelSeq (fun a : Fin k => label (sigma a)) := by
  rfl

theorem IsAltNeg_iff_labelSeq {k m n : ℕ}
    {label : NonzeroSignedSubset n → SignedLabel m}
    {sigma : Fin k → NonzeroSignedSubset n} :
    IsAltNeg label sigma ↔ IsAltNegLabelSeq (fun a : Fin k => label (sigma a)) := by
  rfl



theorem simplexAltPosDeletionSet_eq_labelSeqAltPosDeletionSet {k m n : ℕ}
    (label : NonzeroSignedSubset n → SignedLabel m)
    (sigma : Fin (k + 1) → NonzeroSignedSubset n) :
    simplexAltPosDeletionSet label sigma =
      labelSeqAltPosDeletionSet (fun a : Fin (k + 1) => label (sigma a)) := by
  classical
  ext j
  simp [simplexAltPosDeletionSet, labelSeqAltPosDeletionSet, IsAltPos_iff_labelSeq]



theorem labelSeqSet_comp_perm {k m : ℕ} (L : Fin k → SignedLabel m)
    (e : Equiv.Perm (Fin k)) :
    labelSeqSet (fun a : Fin k => L (e a)) = labelSeqSet L := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
    exact Finset.mem_image.mpr ⟨e a, Finset.mem_univ _, ha⟩
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
    exact Finset.mem_image.mpr ⟨e.symm a, Finset.mem_univ _, by simpa using ha⟩

theorem IsAltPosLabelSeq_comp_perm {k m : ℕ} (L : Fin k → SignedLabel m)
    (e : Equiv.Perm (Fin k)) :
    IsAltPosLabelSeq (fun a : Fin k => L (e a)) ↔ IsAltPosLabelSeq L := by
  unfold IsAltPosLabelSeq
  rw [labelSeqSet_comp_perm L e]

theorem IsAltNegLabelSeq_comp_perm {k m : ℕ} (L : Fin k → SignedLabel m)
    (e : Equiv.Perm (Fin k)) :
    IsAltNegLabelSeq (fun a : Fin k => L (e a)) ↔ IsAltNegLabelSeq L := by
  unfold IsAltNegLabelSeq
  rw [labelSeqSet_comp_perm L e]

theorem labelSeqSet_delete_comp_perm_eq {k m : ℕ}
    (L : Fin (k + 1) → SignedLabel m) (e : Equiv.Perm (Fin (k + 1)))
    (j : Fin (k + 1)) :
    labelSeqSet (fun a : Fin k => L (e (j.succAbove a))) =
      labelSeqSet (fun a : Fin k => L ((e j).succAbove a)) := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
    have hne : e (j.succAbove a) ≠ e j :=
      e.injective.ne (Fin.succAbove_ne j a)
    rcases Fin.exists_succAbove_eq hne with ⟨b, hb⟩
    exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, by simpa [← hb] using ha⟩
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨b, _hb, hb⟩
    let y : Fin (k + 1) := (e j).succAbove b
    have hne_pre : e.symm y ≠ j := by
      intro hy
      have hy' : y = e j := by
        calc
          y = e (e.symm y) := by simp [y]
          _ = e j := by rw [hy]
      exact Fin.succAbove_ne (e j) b (by simpa [y] using hy')
    rcases Fin.exists_succAbove_eq hne_pre with ⟨a, ha⟩
    have hey : e (j.succAbove a) = y := by
      rw [ha]
      simp [y]
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, by simpa [y, ← hey] using hb⟩

theorem IsAltPosLabelSeq_delete_comp_perm_iff {k m : ℕ}
    (L : Fin (k + 1) → SignedLabel m) (e : Equiv.Perm (Fin (k + 1)))
    (j : Fin (k + 1)) :
    IsAltPosLabelSeq (fun a : Fin k => L (e (j.succAbove a))) ↔
      IsAltPosLabelSeq (fun a : Fin k => L ((e j).succAbove a)) := by
  unfold IsAltPosLabelSeq
  rw [labelSeqSet_delete_comp_perm_eq L e j]



theorem labelSeqAltPosDeletionSet_comp_perm_card {k m : ℕ}
    (L : Fin (k + 1) → SignedLabel m) (e : Equiv.Perm (Fin (k + 1))) :
    (labelSeqAltPosDeletionSet (fun a : Fin (k + 1) => L (e a))).card =
      (labelSeqAltPosDeletionSet L).card := by
  classical
  have hmap :
      (labelSeqAltPosDeletionSet (fun a : Fin (k + 1) => L (e a))).map e.toEmbedding =
        labelSeqAltPosDeletionSet L := by
    ext j
    constructor
    · intro hj
      rcases Finset.mem_map.mp hj with ⟨i, hi, hij⟩
      subst j
      have hi' : IsAltPosLabelSeq (fun a : Fin k => L (e (i.succAbove a))) := by
        simpa [labelSeqAltPosDeletionSet] using hi
      have hiff := IsAltPosLabelSeq_delete_comp_perm_iff L e i
      simpa [labelSeqAltPosDeletionSet] using hiff.mp hi'
    · intro hj
      have hj' : IsAltPosLabelSeq (fun a : Fin k => L (j.succAbove a)) := by
        simpa [labelSeqAltPosDeletionSet] using hj
      let i : Fin (k + 1) := e.symm j
      have hiff := IsAltPosLabelSeq_delete_comp_perm_iff L e i
      have hi' : IsAltPosLabelSeq (fun a : Fin k => L (e (i.succAbove a))) := by
        apply hiff.mpr
        simpa [i] using hj'
      refine Finset.mem_map.mpr ⟨i, ?_, by simp [i]⟩
      simpa [labelSeqAltPosDeletionSet] using hi'
  calc
    (labelSeqAltPosDeletionSet (fun a : Fin (k + 1) => L (e a))).card =
        ((labelSeqAltPosDeletionSet (fun a : Fin (k + 1) => L (e a))).map e.toEmbedding).card := by
          rw [Finset.card_map]
    _ = (labelSeqAltPosDeletionSet L).card := by rw [hmap]

theorem permutedSortedLabelSeq_deletionParity {k m : ℕ}
    (L : Fin (k + 1) → SignedLabel m) (e : Equiv.Perm (Fin (k + 1)))
    {idx : Fin (k + 1) → Fin m} (hidx : StrictMono idx)
    {sgn : Fin (k + 1) → Bool}
    (hLsort :
      ∀ a : Fin (k + 1), L (e a) = { positive := sgn a, index := idx a }) :
    Odd (labelSeqAltPosDeletionSet L).card ↔
      IsAltPosLabelSeq L ∨ IsAltNegLabelSeq L := by
  have hsorted :=
    sortedLabelSeq_deletionParity (idx := idx) hidx
      (sgn := sgn) (L := fun a : Fin (k + 1) => L (e a)) hLsort
  rw [labelSeqAltPosDeletionSet_comp_perm_card L e] at hsorted
  exact hsorted.trans
    (or_congr (IsAltPosLabelSeq_comp_perm L e) (IsAltNegLabelSeq_comp_perm L e))





theorem signedLabel_eq_or_eq_neg_of_index_eq {m : ℕ} (A B : SignedLabel m)
    (hidx : A.index = B.index) : A = B ∨ A = B.neg := by
  cases A with
  | mk apos aidx =>
      cases B with
      | mk bpos bidx =>
          dsimp at hidx
          subst aidx
          cases apos <;> cases bpos <;>
            simp [SignedLabel.neg]

theorem labelSeq_index_injective_of_injective_of_noOpposite {k m : ℕ}
    {L : Fin k → SignedLabel m} (hinj : Function.Injective L)
    (hno : NoOppositeLabelSeq L) :
    Function.Injective fun i : Fin k => (L i).index := by
  intro i j hidx
  rcases signedLabel_eq_or_eq_neg_of_index_eq (L i) (L j) hidx with h | h
  · exact hinj h
  · exact False.elim (hno i j h)

theorem labelSeq_deletionParity_of_injective_of_noOpposite {k m : ℕ}
    {L : Fin (k + 1) → SignedLabel m} (hinj : Function.Injective L)
    (hno : NoOppositeLabelSeq L) :
    Odd (labelSeqAltPosDeletionSet L).card ↔
      IsAltPosLabelSeq L ∨ IsAltNegLabelSeq L := by
  classical
  let idxOf : Fin (k + 1) → Fin m := fun a => (L a).index
  let e : Equiv.Perm (Fin (k + 1)) := Tuple.sort idxOf
  let idx : Fin (k + 1) → Fin m := fun a => idxOf (e a)
  let sgn : Fin (k + 1) → Bool := fun a => (L (e a)).positive
  have hidxOf : Function.Injective idxOf :=
    labelSeq_index_injective_of_injective_of_noOpposite
      (L := L) hinj hno
  have hidx_inj : Function.Injective idx := by
    intro a b hab
    apply e.injective
    exact hidxOf hab
  have hidx_mono : Monotone idx := by
    exact Tuple.monotone_sort idxOf
  have hidx : StrictMono idx :=
    hidx_mono.strictMono_of_injective hidx_inj
  have hLsort :
      ∀ a : Fin (k + 1), L (e a) = { positive := sgn a, index := idx a } := by
    intro a
    apply SignedLabel.ext <;> rfl
  exact permutedSortedLabelSeq_deletionParity
    (L := L) e (idx := idx) hidx (sgn := sgn) hLsort

/-! ## Ky Fan parity statement on the non-degenerate range -/



theorem alternatingPrefixLabelChains_card_one_any {m : ℕ}
    (label : NonzeroSignedSubset 1 → SignedLabel m) :
    (alternatingPrefixLabelChains label).card = 2 := by
  classical
  have huniv : alternatingPrefixLabelChains label = (Finset.univ : Finset (SignedPermutation 1)) := by
    ext P
    simp only [alternatingPrefixLabelChains, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, positiveAlternatingPrefixLabelChains,
      negativeAlternatingPrefixLabelChains, PositiveAlternatingPrefixLabels,
      NegativeAlternatingPrefixLabels]
    constructor
    · intro _
      trivial
    · intro _
      have hstrict : StrictMono fun i : Fin 1 => (label (P.prefixChain i)).index := by
        intro a b hab
        fin_cases a
        fin_cases b
        omega
      cases h : (label (P.prefixChain 0)).positive
      · right
        refine ⟨hstrict, ?_⟩
        intro i
        fin_cases i
        simp [h]
      · left
        refine ⟨hstrict, ?_⟩
        intro i
        fin_cases i
        simp [h]
  rw [huniv]
  calc
    (Finset.univ : Finset (SignedPermutation 1)).card =
        Fintype.card (SignedPermutation 1) := by
      simp
    _ = Fintype.card (Equiv.Perm (Fin 1) × (Fin 1 → Bool)) :=
      Fintype.card_congr (signedPermutationEquiv 1)
    _ = 2 := by simp

/-- Base case of the non-degenerate Ky Fan parity statement: for `r = 1` and
any nonempty label set, the two antipodal vertices have opposite signs, hence
exactly one positive-first chain. -/
theorem kyFanParityStatement_one {m : ℕ} (_hm : 1 ≤ m) :
    KyFanParityStatement 1 m := by
  intro _hr _hm label hantipodal _hno
  have halt := alternatingPrefixLabelChains_card_one_any label
  have htwice := alternatingPrefixLabelChains_card (n := 1) (m := m) (by omega) label hantipodal
  rw [halt] at htwice
  have hpos : (positiveAlternatingPrefixLabelChains label).card = 1 := by
    omega
  rw [hpos]
  exact odd_one





























theorem sigmaDeletionHasAlternatingLabelSetOf_duplicate_of_door {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra t : Fin (r + 1)} {k : Fin r}
    (hdoor : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra)
    (hextra : sigmaLabel extra = alternatingLabelOf idx k)
    (htne : t ≠ extra)
    (htlabel : sigmaLabel t = alternatingLabelOf idx k) :
    SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel t := by
  intro a
  by_cases hak : a = k
  · subst a
    exact ⟨extra, by simpa [ne_eq, eq_comm] using htne, hextra⟩
  · rcases hdoor a with ⟨u, hune, hulabel⟩
    refine ⟨u, ?_, hulabel⟩
    intro hut
    subst u
    have hka : k = a := by
      apply (alternatingLabelOf_inj hidx).mp
      exact htlabel.symm.trans hulabel
    exact hak hka.symm

theorem sigmaDeletionHasAlternatingLabelSetOf_retained_image_eq {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)}
    (hdoor : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra) :
    ((Finset.univ.erase extra).image sigmaLabel) = alternatingLabelSetOf idx := by
  classical
  let retained : Finset (Fin (r + 1)) := Finset.univ.erase extra
  have hA_subset :
      alternatingLabelSetOf idx ⊆ retained.image sigmaLabel := by
    intro L hL
    rcases (by simpa [alternatingLabelSetOf] using hL) with ⟨a, ha⟩
    rcases hdoor a with ⟨t, htne, htlabel⟩
    exact Finset.mem_image.mpr ⟨t, by simp [retained, htne], htlabel.trans ha⟩
  have hcard_le :
      (retained.image sigmaLabel).card ≤ (alternatingLabelSetOf idx).card := by
    have himage_le : (retained.image sigmaLabel).card ≤ retained.card :=
      Finset.card_image_le
    have hretained : retained.card = r := by
      simp [retained]
    simpa [alternatingLabelSetOf_card hidx, hretained] using himage_le
  have hEq : alternatingLabelSetOf idx = retained.image sigmaLabel :=
    Finset.eq_of_subset_of_card_le hA_subset hcard_le
  exact hEq.symm

theorem sigmaDeletionHasAlternatingLabelSetOf_retained_injOn {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)}
    (hdoor : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra) :
    Set.InjOn sigmaLabel (Finset.univ.erase extra) := by
  classical
  let retained : Finset (Fin (r + 1)) := Finset.univ.erase extra
  have himage := sigmaDeletionHasAlternatingLabelSetOf_retained_image_eq
    (idx := idx) hidx (sigmaLabel := sigmaLabel) (extra := extra) hdoor
  have hcard :
      (retained.image sigmaLabel).card = retained.card := by
    rw [himage, alternatingLabelSetOf_card hidx]
    simp [retained]
  exact (Finset.card_image_iff).mp hcard

theorem sigmaDoorSetOf_card_duplicate_of_door {r m : ℕ}
    {idx : Fin r → Fin m} (hidx : Function.Injective idx)
    {sigmaLabel : Fin (r + 1) → SignedLabel m} {extra : Fin (r + 1)} {k : Fin r}
    (hdoorExtra : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel extra)
    (hextra : sigmaLabel extra = alternatingLabelOf idx k) :
    (sigmaDoorSetOf idx sigmaLabel).card = 2 := by
  classical
  rcases hdoorExtra k with ⟨t, htne, htlabel⟩
  have htDoor : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel t :=
    sigmaDeletionHasAlternatingLabelSetOf_duplicate_of_door
      (idx := idx) hidx (extra := extra) (t := t) (k := k)
      hdoorExtra hextra htne htlabel
  have hinj :=
    sigmaDeletionHasAlternatingLabelSetOf_retained_injOn
      (idx := idx) hidx (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have himage :=
    sigmaDeletionHasAlternatingLabelSetOf_retained_image_eq
      (idx := idx) hidx (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have hmem_imp :
      ∀ j, j ∈ sigmaDoorSetOf idx sigmaLabel → j = extra ∨ j = t := by
    intro j hj
    have hdoorj : SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel j := by
      simpa [sigmaDoorSetOf] using hj
    by_cases hjextra : j = extra
    · exact Or.inl hjextra
    · right
      have hjret : j ∈ (Finset.univ.erase extra : Finset (Fin (r + 1))) := by
        simp [hjextra]
      have hjimage : sigmaLabel j ∈ (Finset.univ.erase extra).image sigmaLabel :=
        Finset.mem_image.mpr ⟨j, hjret, rfl⟩
      rw [himage] at hjimage
      rcases (by simpa [alternatingLabelSetOf] using hjimage) with ⟨b, hjlabel⟩
      by_cases hbk : b = k
      · subst b
        exact hinj hjret (by simp [htne]) (hjlabel.symm.trans htlabel.symm)
      · rcases hdoorj b with ⟨u, hune, hulabel⟩
        have huneExtra : u ≠ extra := by
          intro hue
          subst u
          have hkb : k = b := (alternatingLabelOf_inj hidx).mp
            (hextra.symm.trans hulabel)
          exact hbk hkb.symm
        have huret : u ∈ (Finset.univ.erase extra : Finset (Fin (r + 1))) := by
          simp [huneExtra]
        have huj : u = j :=
          hinj huret hjret (hulabel.trans hjlabel)
        exact False.elim (hune huj)
  have hset : sigmaDoorSetOf idx sigmaLabel = {extra, t} := by
    ext j
    constructor
    · intro hj
      rcases hmem_imp j hj with rfl | rfl <;> simp
    · intro hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · simpa [sigmaDoorSetOf] using hdoorExtra
      · simpa [sigmaDoorSetOf] using htDoor
  rw [hset]
  exact Finset.card_pair htne.symm





theorem labelSeqSet_delete_eq_erase_image {k m : ℕ}
    (L : Fin (k + 1) → SignedLabel m) (j : Fin (k + 1)) :
    labelSeqSet (fun a : Fin k => L (j.succAbove a)) =
      (Finset.univ.erase j).image L := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨a, _ha, ha⟩
    exact Finset.mem_image.mpr
      ⟨j.succAbove a, by simp [Fin.succAbove_ne], ha⟩
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨t, ht, htlabel⟩
    have htne : t ≠ j := by
      simpa using ht
    rcases Fin.exists_succAbove_eq htne with ⟨a, ha⟩
    exact Finset.mem_image.mpr
      ⟨a, Finset.mem_univ _, by simpa [← ha] using htlabel⟩

theorem SigmaDeletionHasAlternatingLabelSetOf_iff_subset_erase_image {r m : ℕ}
    {idx : Fin r → Fin m} {sigmaLabel : Fin (r + 1) → SignedLabel m}
    {j : Fin (r + 1)} :
    SigmaDeletionHasAlternatingLabelSetOf idx sigmaLabel j ↔
      alternatingLabelSetOf idx ⊆ (Finset.univ.erase j).image sigmaLabel := by
  classical
  constructor
  · intro hdoor x hx
    rcases (by simpa [alternatingLabelSetOf] using hx) with ⟨a, ha⟩
    rcases hdoor a with ⟨t, htne, htlabel⟩
    exact Finset.mem_image.mpr
      ⟨t, by simp [htne], htlabel.trans ha⟩
  · intro hsub a
    have hmem : alternatingLabelOf idx a ∈ alternatingLabelSetOf idx := by
      simp [alternatingLabelSetOf]
    have himage := hsub hmem
    rcases Finset.mem_image.mp himage with ⟨t, ht, htlabel⟩
    have htne : t ≠ j := by
      simpa using ht
    exact ⟨t, htne, htlabel⟩

theorem IsAltPosLabelSeq.injective {k m : ℕ}
    {L : Fin k → SignedLabel m} (h : IsAltPosLabelSeq L) :
    Function.Injective L := by
  classical
  rcases h with ⟨idx, hidx, hset⟩
  have hcard : (labelSeqSet L).card = k := by
    rw [hset, alternatingLabelSetOf_card hidx.injective]
  have hcard_image :
      (Finset.univ.image L).card =
        (Finset.univ : Finset (Fin k)).card := by
    simpa [labelSeqSet] using hcard
  have hinjOn : Set.InjOn L (Finset.univ : Finset (Fin k)) :=
    (Finset.card_image_iff).mp hcard_image
  intro a b hab
  exact hinjOn (by simp) (by simp) hab

theorem IsAltNegLabelSeq.injective {k m : ℕ}
    {L : Fin k → SignedLabel m} (h : IsAltNegLabelSeq L) :
    Function.Injective L := by
  classical
  rcases h with ⟨idx, hidx, hset⟩
  have hcard : (labelSeqSet L).card = k := by
    rw [hset, alternatingNegLabelSetOf_card hidx.injective]
  have hcard_image :
      (Finset.univ.image L).card =
        (Finset.univ : Finset (Fin k)).card := by
    simpa [labelSeqSet] using hcard
  have hinjOn : Set.InjOn L (Finset.univ : Finset (Fin k)) :=
    (Finset.card_image_iff).mp hcard_image
  intro a b hab
  exact hinjOn (by simp) (by simp) hab

theorem IsAltPosLabelSeq_delete_iff_sigmaDeletionOf_of_original_alt {k m : ℕ}
    {idx : Fin k → Fin m} (hidx : StrictMono idx)
    {L : Fin (k + 1) → SignedLabel m}
    (horig : labelSeqSet L = alternatingLabelSetOf idx)
    (j : Fin (k + 1)) :
    IsAltPosLabelSeq (fun a : Fin k => L (j.succAbove a)) ↔
      SigmaDeletionHasAlternatingLabelSetOf idx L j := by
  classical
  constructor
  · intro hdel
    rcases hdel with ⟨eta, heta, hdelSet⟩
    let retained : Finset (Fin (k + 1)) := Finset.univ.erase j
    have hret_eq_del :
        labelSeqSet (fun a : Fin k => L (j.succAbove a)) =
          retained.image L := by
      simpa [retained] using labelSeqSet_delete_eq_erase_image L j
    have hret_subset :
        retained.image L ⊆ alternatingLabelSetOf idx := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨t, _ht, htlabel⟩
      have hxorig : x ∈ labelSeqSet L := by
        rw [← htlabel]
        simp [labelSeqSet]
      simpa [horig] using hxorig
    have hret_card : (retained.image L).card = k := by
      rw [← hret_eq_del, hdelSet, alternatingLabelSetOf_card heta.injective]
    have halt_card : (alternatingLabelSetOf idx).card = k :=
      alternatingLabelSetOf_card hidx.injective
    have hret_eq_alt : retained.image L = alternatingLabelSetOf idx := by
      apply Finset.eq_of_subset_of_card_le hret_subset
      rw [hret_card, halt_card]
    exact SigmaDeletionHasAlternatingLabelSetOf_iff_subset_erase_image.mpr
      (by simpa [retained, hret_eq_alt])
  · intro hdoor
    refine ⟨idx, hidx, ?_⟩
    have himage :=
      sigmaDeletionHasAlternatingLabelSetOf_retained_image_eq
        (idx := idx) hidx.injective (sigmaLabel := L) (extra := j) hdoor
    rw [labelSeqSet_delete_eq_erase_image, himage]

theorem labelSeq_deletionParity_of_not_injective_of_noOpposite {k m : ℕ}
    {L : Fin (k + 1) → SignedLabel m} (hnot : ¬ Function.Injective L)
    (_hno : NoOppositeLabelSeq L) :
    Even (labelSeqAltPosDeletionSet L).card ∧
      ¬ IsAltPosLabelSeq L ∧ ¬ IsAltNegLabelSeq L := by
  classical
  have hnotAltPos : ¬ IsAltPosLabelSeq L := by
    intro h
    exact hnot h.injective
  have hnotAltNeg : ¬ IsAltNegLabelSeq L := by
    intro h
    exact hnot h.injective
  have heven : Even (labelSeqAltPosDeletionSet L).card := by
    by_cases hnonempty : (labelSeqAltPosDeletionSet L).Nonempty
    · rcases hnonempty with ⟨j0, hj0⟩
      have hdel0 :
          IsAltPosLabelSeq (fun a : Fin k => L (j0.succAbove a)) := by
        simpa [labelSeqAltPosDeletionSet] using hj0
      rcases hdel0 with ⟨idx, hidx, hdelSet⟩
      let retained : Finset (Fin (k + 1)) := Finset.univ.erase j0
      have hret_eq_del :
          labelSeqSet (fun a : Fin k => L (j0.succAbove a)) =
            retained.image L := by
        simpa [retained] using labelSeqSet_delete_eq_erase_image L j0
      have hret_eq_alt : retained.image L = alternatingLabelSetOf idx := by
        rw [← hret_eq_del, hdelSet]
      have hret_subset_orig : retained.image L ⊆ labelSeqSet L := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨t, _ht, htlabel⟩
        rw [← htlabel]
        simp [labelSeqSet]
      have hcard_orig_le : (labelSeqSet L).card ≤ k := by
        have himage_le :
            (labelSeqSet L).card ≤ k + 1 := by
          simpa [labelSeqSet] using
            (Finset.card_image_le :
              (Finset.univ.image L).card ≤
                (Finset.univ : Finset (Fin (k + 1))).card)
        have hneq : (labelSeqSet L).card ≠ k + 1 := by
          intro hcard
          have hcard_image :
              (Finset.univ.image L).card =
                (Finset.univ : Finset (Fin (k + 1))).card := by
            simpa [labelSeqSet] using hcard
          have hinjOn : Set.InjOn L (Finset.univ : Finset (Fin (k + 1))) :=
            (Finset.card_image_iff).mp hcard_image
          exact hnot (by
            intro a b hab
            exact hinjOn (by simp) (by simp) hab)
        omega
      have hcard_ret : (retained.image L).card = k := by
        rw [hret_eq_alt, alternatingLabelSetOf_card hidx.injective]
      have hcard_orig_ge : k ≤ (labelSeqSet L).card := by
        have hle : (retained.image L).card ≤ (labelSeqSet L).card :=
          Finset.card_le_card hret_subset_orig
        omega
      have hcard_orig : (labelSeqSet L).card = k := by
        omega
      have hret_eq_orig : retained.image L = labelSeqSet L := by
        apply Finset.eq_of_subset_of_card_le hret_subset_orig
        rw [hcard_orig, hcard_ret]
      have horig : labelSeqSet L = alternatingLabelSetOf idx := by
        rw [← hret_eq_orig, hret_eq_alt]
      have hdoor0 : SigmaDeletionHasAlternatingLabelSetOf idx L j0 := by
        exact (IsAltPosLabelSeq_delete_iff_sigmaDeletionOf_of_original_alt
          (idx := idx) hidx (L := L) horig j0).mp
          ⟨idx, hidx, hdelSet⟩
      have hextra_mem : L j0 ∈ alternatingLabelSetOf idx := by
        have hmem : L j0 ∈ labelSeqSet L := by
          simp [labelSeqSet]
        simpa [horig] using hmem
      rcases (by simpa [alternatingLabelSetOf] using hextra_mem) with ⟨a, ha⟩
      have hextra : L j0 = alternatingLabelOf idx a := ha.symm
      have hfixedCard :
          (sigmaDoorSetOf idx L).card = 2 :=
        sigmaDoorSetOf_card_duplicate_of_door
          (idx := idx) hidx.injective (sigmaLabel := L) (extra := j0)
          (k := a) hdoor0 hextra
      have hset :
          labelSeqAltPosDeletionSet L = sigmaDoorSetOf idx L := by
        ext j
        simp [labelSeqAltPosDeletionSet, sigmaDoorSetOf,
          IsAltPosLabelSeq_delete_iff_sigmaDeletionOf_of_original_alt
            (idx := idx) hidx (L := L) horig j]
      rw [hset, hfixedCard]
      simp
    · have hempty : labelSeqAltPosDeletionSet L = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hnonempty
      rw [hempty]
      simp
  exact ⟨heven, hnotAltPos, hnotAltNeg⟩

theorem labelSeq_deletionParity_of_noOpposite {k m : ℕ}
    {L : Fin (k + 1) → SignedLabel m} (hno : NoOppositeLabelSeq L) :
    Odd (labelSeqAltPosDeletionSet L).card ↔
      IsAltPosLabelSeq L ∨ IsAltNegLabelSeq L := by
  classical
  by_cases hinj : Function.Injective L
  · exact labelSeq_deletionParity_of_injective_of_noOpposite
      (L := L) hinj hno
  · rcases labelSeq_deletionParity_of_not_injective_of_noOpposite
      (L := L) hinj hno with ⟨heven, hnotPos, hnotNeg⟩
    constructor
    · intro hodd
      rcases hodd with ⟨a, ha⟩
      rcases heven with ⟨b, hb⟩
      omega
    · intro h
      rcases h with hpos | hneg
      · exact False.elim (hnotPos hpos)
      · exact False.elim (hnotNeg hneg)

theorem simplex_deletionParity_of_noOpposite {k m n : ℕ}
    {label : NonzeroSignedSubset n → SignedLabel m}
    {sigma : Fin (k + 1) → NonzeroSignedSubset n}
    (hno : NoOppositeLabelSeq (fun a : Fin (k + 1) => label (sigma a))) :
    Odd (simplexAltPosDeletionSet label sigma).card ↔
      IsAltPos label sigma ∨ IsAltNeg label sigma := by
  rw [simplexAltPosDeletionSet_eq_labelSeqAltPosDeletionSet]
  exact (labelSeq_deletionParity_of_noOpposite
    (L := fun a : Fin (k + 1) => label (sigma a)) hno).trans
    (or_congr IsAltPos_iff_labelSeq.symm IsAltNeg_iff_labelSeq.symm)

















/-! ## Rho-degree and Fan handshaking interfaces

The next declarations isolate the finite parity core used by the hemisphere
argument.  The geometric degree facts are stated on nonempty, concrete finite
types; the parity theorem itself is the standard bipartite handshaking count
modulo two.
-/

theorem finset_card_filter_cast_zmod_two {α : Type*}
    (s : Finset α) (p : α → Prop) [DecidablePred p] :
    ((s.filter p).card : ZMod 2) =
      ∑ x ∈ s, if p x then (1 : ZMod 2) else 0 := by
  rw [Finset.sum_boole]

theorem fintype_card_subtype_cast_zmod_two {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] :
    (Fintype.card {x : α // p x} : ZMod 2) =
      ∑ x : α, if p x then (1 : ZMod 2) else 0 := by
  classical
  rw [← finset_card_filter_cast_zmod_two (Finset.univ : Finset α) p]
  exact congrArg (fun n : ℕ => (n : ZMod 2)) (Fintype.card_subtype p)

/-- In a finite bipartite graph, the number of odd-degree vertices on the
left equals the number of odd-degree vertices on the right modulo two. -/
theorem bipartite_odd_degree_card_eq_mod_two
    {R S : Type*} [Fintype R] [Fintype S]
    (edge : R → S → Prop) [DecidableRel edge] :
    (Fintype.card {r : R // Odd (Fintype.card {s : S // edge r s})} : ZMod 2) =
      (Fintype.card {s : S // Odd (Fintype.card {r : R // edge r s})} : ZMod 2) := by
  classical
  rw [fintype_card_subtype_cast_zmod_two, fintype_card_subtype_cast_zmod_two]
  calc
    (∑ r : R, if Odd (Fintype.card {s : S // edge r s}) then (1 : ZMod 2) else 0)
        = ∑ r : R, (Fintype.card {s : S // edge r s} : ZMod 2) := by
          refine Finset.sum_congr rfl ?_
          intro r _hr
          by_cases hodd : Odd (Fintype.card {s : S // edge r s})
          · rw [if_pos hodd]
            exact hodd.natCast_zmod_two.symm
          · rw [if_neg hodd]
            have heven : Even (Fintype.card {s : S // edge r s}) :=
              Nat.not_odd_iff_even.mp hodd
            exact heven.natCast_zmod_two.symm
    _ = ∑ r : R, ∑ s : S, if edge r s then (1 : ZMod 2) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro r _hr
          rw [← fintype_card_subtype_cast_zmod_two (fun s : S => edge r s)]
    _ = ∑ s : S, ∑ r : R, if edge r s then (1 : ZMod 2) else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ s : S, (Fintype.card {r : R // edge r s} : ZMod 2) := by
          refine Finset.sum_congr rfl ?_
          intro s _hs
          rw [← fintype_card_subtype_cast_zmod_two (fun r : R => edge r s)]
    _ = ∑ s : S, if Odd (Fintype.card {r : R // edge r s}) then (1 : ZMod 2) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro s _hs
          by_cases hodd : Odd (Fintype.card {r : R // edge r s})
          · rw [if_pos hodd]
            exact hodd.natCast_zmod_two
          · rw [if_neg hodd]
            have heven : Even (Fintype.card {r : R // edge r s}) :=
              Nat.not_odd_iff_even.mp hodd
            exact heven.natCast_zmod_two

theorem bipartite_boundary_top_parity
    {R S : Type*} [Fintype R] [Fintype S]
    (edge : R → S → Prop) [DecidableRel edge]
    (boundary : R → Prop) [DecidablePred boundary]
    (topOdd : S → Prop) [DecidablePred topOdd]
    (hr :
      ∀ r : R,
        (Odd (Fintype.card {s : S // edge r s}) ↔ boundary r))
    (hs :
      ∀ s : S,
        (Odd (Fintype.card {r : R // edge r s}) ↔ topOdd s)) :
    (Fintype.card {r : R // boundary r} : ZMod 2) =
      (Fintype.card {s : S // topOdd s} : ZMod 2) := by
  classical
  have hodd := bipartite_odd_degree_card_eq_mod_two (R := R) (S := S) edge
  have hR :
      Fintype.card {r : R // Odd (Fintype.card {s : S // edge r s})} =
        Fintype.card {r : R // boundary r} := by
    exact Fintype.card_congr
      { toFun := fun r => ⟨r.1, (hr r.1).mp r.2⟩
        invFun := fun r => ⟨r.1, (hr r.1).mpr r.2⟩
        left_inv := by intro r; cases r; rfl
        right_inv := by intro r; cases r; rfl }
  have hS :
      Fintype.card {s : S // Odd (Fintype.card {r : R // edge r s})} =
        Fintype.card {s : S // topOdd s} := by
    exact Fintype.card_congr
      { toFun := fun s => ⟨s.1, (hs s.1).mp s.2⟩
        invFun := fun s => ⟨s.1, (hs s.1).mpr s.2⟩
        left_inv := by intro s; cases s; rfl
        right_inv := by intro s; cases s; rfl }
  simpa [hR, hS] using hodd



namespace RhoDegreeManifoldData



theorem odd_degree_iff_boundary
    {R S : Type*} [Fintype R] [Fintype S]
    (D : RhoDegreeManifoldData R S) (r : R) :
    Odd (Fintype.card {s : S // D.edge r s}) ↔ D.boundary r := by
  rw [D.degree_card r]
  by_cases hb : D.boundary r <;> simp [hb]

theorem boundary_top_parity
    {R S : Type*} [Fintype R] [Fintype S]
    (D : RhoDegreeManifoldData R S)
    (topOdd : S → Prop) [DecidablePred topOdd]
    (hs :
      ∀ s : S,
        (Odd (Fintype.card {r : R // D.edge r s}) ↔ topOdd s)) :
    (Fintype.card {r : R // D.boundary r} : ZMod 2) =
      (Fintype.card {s : S // topOdd s} : ZMod 2) := by
  classical
  exact bipartite_boundary_top_parity D.edge D.boundary topOdd
    (D.odd_degree_iff_boundary) hs

end RhoDegreeManifoldData











theorem sigmaDeletionHasAlternatingLabelSet_duplicate_of_door {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra t : Fin (d + 1)} {k : Fin d}
    (hdoor : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra)
    (hextra : sigmaLabel extra = alternatingLabel k)
    (htne : t ≠ extra)
    (htlabel : sigmaLabel t = alternatingLabel k) :
    SigmaDeletionHasAlternatingLabelSet sigmaLabel t := by
  intro a
  by_cases hak : a = k
  · subst a
    exact ⟨extra, by simpa [ne_eq, eq_comm] using htne, hextra⟩
  · rcases hdoor a with ⟨u, hune, hulabel⟩
    refine ⟨u, ?_, hulabel⟩
    intro hut
    subst u
    have hka : k = a := by
      apply alternatingLabel_inj.mp
      exact htlabel.symm.trans hulabel
    exact hak hka.symm

theorem sigmaDeletionHasAlternatingLabelSet_retained_image_eq {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)}
    (hdoor : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra) :
    ((Finset.univ.erase extra).image sigmaLabel) = alternatingLabelSetA d := by
  classical
  let retained : Finset (Fin (d + 1)) := Finset.univ.erase extra
  have hA_subset :
      alternatingLabelSetA d ⊆ retained.image sigmaLabel := by
    intro L hL
    rcases (by simpa [alternatingLabelSetA] using hL) with ⟨a, ha⟩
    rcases hdoor a with ⟨t, htne, htlabel⟩
    exact Finset.mem_image.mpr ⟨t, by simp [retained, htne], htlabel.trans ha⟩
  have hcard_le :
      (retained.image sigmaLabel).card ≤ (alternatingLabelSetA d).card := by
    have himage_le : (retained.image sigmaLabel).card ≤ retained.card :=
      Finset.card_image_le
    have hretained : retained.card = d := by
      simp [retained]
    simpa [alternatingLabelSetA_card, hretained] using himage_le
  have hEq : alternatingLabelSetA d = retained.image sigmaLabel :=
    Finset.eq_of_subset_of_card_le hA_subset hcard_le
  exact hEq.symm

theorem sigmaDeletionHasAlternatingLabelSet_retained_injOn {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)}
    (hdoor : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra) :
    Set.InjOn sigmaLabel (Finset.univ.erase extra) := by
  classical
  let retained : Finset (Fin (d + 1)) := Finset.univ.erase extra
  have himage := sigmaDeletionHasAlternatingLabelSet_retained_image_eq
    (sigmaLabel := sigmaLabel) (extra := extra) hdoor
  have hcard :
      (retained.image sigmaLabel).card = retained.card := by
    rw [himage, alternatingLabelSetA_card]
    simp [retained]
  exact (Finset.card_image_iff).mp hcard

theorem sigmaDoorSet_card_duplicate_of_door {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)} {k : Fin d}
    (hdoorExtra : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra)
    (hextra : sigmaLabel extra = alternatingLabel k) :
    (sigmaDoorSet sigmaLabel).card = 2 := by
  classical
  rcases hdoorExtra k with ⟨t, htne, htlabel⟩
  have htDoor : SigmaDeletionHasAlternatingLabelSet sigmaLabel t :=
    sigmaDeletionHasAlternatingLabelSet_duplicate_of_door
      (extra := extra) (t := t) (k := k) hdoorExtra hextra htne htlabel
  have hinj :=
    sigmaDeletionHasAlternatingLabelSet_retained_injOn
      (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have himage :=
    sigmaDeletionHasAlternatingLabelSet_retained_image_eq
      (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have hmem_imp :
      ∀ j, j ∈ sigmaDoorSet sigmaLabel → j = extra ∨ j = t := by
    intro j hj
    have hdoorj : SigmaDeletionHasAlternatingLabelSet sigmaLabel j := by
      simpa [sigmaDoorSet] using hj
    by_cases hjextra : j = extra
    · exact Or.inl hjextra
    · right
      have hjret : j ∈ (Finset.univ.erase extra : Finset (Fin (d + 1))) := by
        simp [hjextra]
      have hjimage : sigmaLabel j ∈ (Finset.univ.erase extra).image sigmaLabel :=
        Finset.mem_image.mpr ⟨j, hjret, rfl⟩
      rw [himage] at hjimage
      rcases (by simpa [alternatingLabelSetA] using hjimage) with ⟨b, hjlabel⟩
      by_cases hbk : b = k
      · subst b
        exact hinj hjret (by simp [htne]) (hjlabel.symm.trans htlabel.symm)
      · rcases hdoorj b with ⟨u, hune, hulabel⟩
        have huneExtra : u ≠ extra := by
          intro hue
          subst u
          have hkb : k = b := alternatingLabel_inj.mp (hextra.symm.trans hulabel)
          exact hbk hkb.symm
        have huret : u ∈ (Finset.univ.erase extra : Finset (Fin (d + 1))) := by
          simp [huneExtra]
        have huj : u = j :=
          hinj huret hjret (hulabel.trans hjlabel)
        exact False.elim (hune huj)
  have hset : sigmaDoorSet sigmaLabel = {extra, t} := by
    ext j
    constructor
    · intro hj
      rcases hmem_imp j hj with rfl | rfl <;> simp
    · intro hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · simpa [sigmaDoorSet] using hdoorExtra
      · simpa [sigmaDoorSet] using htDoor
  rw [hset]
  exact Finset.card_pair htne.symm

theorem sigmaDoorSet_card_opposite_of_door {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)} {k : Fin d}
    (hdoorExtra : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra)
    (hextra : sigmaLabel extra = (alternatingLabel k).neg) :
    (sigmaDoorSet sigmaLabel).card = 1 := by
  classical
  have hinj :=
    sigmaDeletionHasAlternatingLabelSet_retained_injOn
      (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have himage :=
    sigmaDeletionHasAlternatingLabelSet_retained_image_eq
      (sigmaLabel := sigmaLabel) (extra := extra) hdoorExtra
  have hmem_imp :
      ∀ j, j ∈ sigmaDoorSet sigmaLabel → j = extra := by
    intro j hj
    have hdoorj : SigmaDeletionHasAlternatingLabelSet sigmaLabel j := by
      simpa [sigmaDoorSet] using hj
    by_cases hjextra : j = extra
    · exact hjextra
    · have hjret : j ∈ (Finset.univ.erase extra : Finset (Fin (d + 1))) := by
        simp [hjextra]
      have hjimage : sigmaLabel j ∈ (Finset.univ.erase extra).image sigmaLabel :=
        Finset.mem_image.mpr ⟨j, hjret, rfl⟩
      rw [himage] at hjimage
      rcases (by simpa [alternatingLabelSetA] using hjimage) with ⟨b, hjlabel⟩
      rcases hdoorj b with ⟨u, hune, hulabel⟩
      have huneExtra : u ≠ extra := by
        intro hue
        subst u
        exact alternatingLabel_neg_ne k b (hextra.symm.trans hulabel)
      have huret : u ∈ (Finset.univ.erase extra : Finset (Fin (d + 1))) := by
        simp [huneExtra]
      have huj : u = j :=
        hinj huret hjret (hulabel.trans hjlabel)
      exact False.elim (hune huj)
  have hset : sigmaDoorSet sigmaLabel = {extra} := by
    ext j
    constructor
    · intro hj
      exact by simpa using hmem_imp j hj
    · intro hj
      simp only [Finset.mem_singleton] at hj
      subst j
      simpa [sigmaDoorSet] using hdoorExtra
  rw [hset]
  simp

theorem sigmaDoorSet_odd_iff_card_one_of_door {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)}
    (hdoorExtra : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra) :
    Odd (sigmaDoorSet sigmaLabel).card ↔ (sigmaDoorSet sigmaLabel).card = 1 := by
  rcases signedLabel_eq_alternating_or_neg (sigmaLabel extra) with hpos | hneg
  · have hcard :=
      sigmaDoorSet_card_duplicate_of_door (sigmaLabel := sigmaLabel)
        (extra := extra) (k := (sigmaLabel extra).index) hdoorExtra hpos
    rw [hcard]
    simp
  · have hcard :=
      sigmaDoorSet_card_opposite_of_door (sigmaLabel := sigmaLabel)
        (extra := extra) (k := (sigmaLabel extra).index) hdoorExtra hneg
    rw [hcard]
    simp

theorem sigmaDoorSet_card_one_gives_chain_complementary_pair_of_door {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)}
    (hdoorExtra : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra)
    (hcard : (sigmaDoorSet sigmaLabel).card = 1) :
    ∃ i j : Fin (d + 1), i ≠ j ∧
      (sigmaLabel i).index = (sigmaLabel j).index ∧
      (sigmaLabel i).positive ≠ (sigmaLabel j).positive := by
  classical
  have hextra_mem : extra ∈ sigmaDoorSet sigmaLabel := by
    simpa [sigmaDoorSet] using hdoorExtra
  rcases signedLabel_eq_alternating_or_neg (sigmaLabel extra) with hpos | hneg
  · let k : Fin d := (sigmaLabel extra).index
    rcases hdoorExtra k with ⟨t, htne, htlabel⟩
    have htdoor : SigmaDeletionHasAlternatingLabelSet sigmaLabel t :=
      sigmaDeletionHasAlternatingLabelSet_duplicate_of_door
        (extra := extra) (t := t) (k := k) hdoorExtra hpos htne htlabel
    have ht_mem : t ∈ sigmaDoorSet sigmaLabel := by
      simpa [sigmaDoorSet] using htdoor
    have hle : (sigmaDoorSet sigmaLabel).card ≤ 1 := by omega
    have hteq : t = extra :=
      (Finset.card_le_one_iff.mp hle) ht_mem hextra_mem
    exact False.elim (htne hteq)
  · let k : Fin d := (sigmaLabel extra).index
    rcases hdoorExtra k with ⟨t, htne, htlabel⟩
    refine ⟨extra, t, htne.symm, ?_, ?_⟩
    · have hcomp : sigmaLabel extra = (sigmaLabel t).neg := by
        rw [htlabel]
        exact hneg
      have hidx := congrArg SignedLabel.index hcomp
      simpa [SignedLabel.neg] using hidx
    · have hcomp : sigmaLabel extra = (sigmaLabel t).neg := by
        rw [htlabel]
        exact hneg
      have hpos' := congrArg SignedLabel.positive hcomp
      cases h₁ : (sigmaLabel extra).positive <;>
        cases h₂ : (sigmaLabel t).positive <;>
          simp [SignedLabel.neg, h₁, h₂] at hpos' ⊢

theorem sigmaDoorSet_card_one_gives_ordered_chain_complementary_pair_of_door {d : ℕ}
    {sigmaLabel : Fin (d + 1) → SignedLabel d} {extra : Fin (d + 1)}
    (hdoorExtra : SigmaDeletionHasAlternatingLabelSet sigmaLabel extra)
    (hcard : (sigmaDoorSet sigmaLabel).card = 1) :
    ∃ i j : Fin (d + 1), i < j ∧
      (sigmaLabel i).index = (sigmaLabel j).index ∧
      (sigmaLabel i).positive ≠ (sigmaLabel j).positive := by
  obtain ⟨i, j, hij, hidx, hsign⟩ :=
    sigmaDoorSet_card_one_gives_chain_complementary_pair_of_door hdoorExtra hcard
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact ⟨i, j, hlt, hidx, hsign⟩
  · exact ⟨j, i, hgt, hidx.symm, hsign.symm⟩

theorem sigmaDoorSet_card_one_gives_prefixChain_complementary_pair_of_door {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    {P : SignedPermutation (d + 1)} {extra : Fin (d + 1)}
    (hdoorExtra :
      SigmaDeletionHasAlternatingLabelSet (fun i => label (P.prefixChain i)) extra)
    (hcard : (sigmaDoorSet (fun i => label (P.prefixChain i))).card = 1) :
    ∃ i j : Fin (d + 1), i < j ∧
      (label (P.prefixChain i)).index = (label (P.prefixChain j)).index ∧
      (label (P.prefixChain i)).positive ≠ (label (P.prefixChain j)).positive :=
  sigmaDoorSet_card_one_gives_ordered_chain_complementary_pair_of_door
    (sigmaLabel := fun i => label (P.prefixChain i)) hdoorExtra hcard

namespace SignedPermutation















































































end SignedPermutation







































/-! ## Actual upper-hemisphere label-set-`A` graph -/































theorem equatorRestrictedLabel_unordered_odd {d : ℕ}
    (hKy : KyFanUnorderedParityStatement d)
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (hno : NoComplementaryComparableLabels label) :
    Odd (Fintype.card (EquatorActualARidge (equatorRestrictedLabel label))) :=
  hKy (equatorRestrictedLabel label)
    (equatorRestrictedLabel_antipodal hantipodal)
    (equatorRestrictedLabel_noComplementary hno)



















theorem actualHemisphereA_sigma_degree_card {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (sigma : ActualHemisphereAChain label) :
    Fintype.card
        {rho : ActualHemisphereARidge label // actualHemisphereAEdge rho sigma} =
      (sigmaDoorSet (fun i => label (sigma.1.prefixChain i))).card := by
  classical
  have hcongr :=
    Fintype.card_congr (actualHemisphereAIncidentDoorEquiv sigma)
  have hdoor :
      Fintype.card
          {j : Fin (d + 1) //
            SigmaDeletionHasAlternatingLabelSet
              (fun i => label (sigma.1.prefixChain i)) j} =
        (sigmaDoorSet (fun i => label (sigma.1.prefixChain i))).card := by
    rw [Fintype.card_subtype]
    rfl
  exact hcongr.trans hdoor

theorem actualHemisphereA_sigma_odd_degree_iff_oneDoor {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (sigma : ActualHemisphereAChain label) :
    Odd
        (Fintype.card
          {rho : ActualHemisphereARidge label // actualHemisphereAEdge rho sigma}) ↔
      actualHemisphereAOneDoor sigma := by
  rcases sigma.2.2 with ⟨gap, hgap⟩
  have hdoorExtra :
      SigmaDeletionHasAlternatingLabelSet (fun i => label (sigma.1.prefixChain i)) gap := by
    intro a
    rcases hgap a with ⟨t, ht⟩
    exact ⟨gap.succAbove t, Fin.succAbove_ne gap t, ht⟩
  rw [actualHemisphereA_sigma_degree_card sigma, actualHemisphereAOneDoor]
  exact sigmaDoorSet_odd_iff_card_one_of_door hdoorExtra



theorem actualHemisphereARidge_nonempty_of_boundary_odd {d : ℕ}
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (hboundaryOdd :
      Odd (Fintype.card
        {rho : ActualHemisphereARidge label //
          actualHemisphereABoundary rho})) :
    Nonempty (ActualHemisphereARidge label) := by
  rcases hboundaryOdd with ⟨k, hk⟩
  have hpos :
      0 < Fintype.card
        {rho : ActualHemisphereARidge label //
          actualHemisphereABoundary rho} := by
    omega
  obtain ⟨rho⟩ := Fintype.card_pos_iff.mp hpos
  exact ⟨rho.1⟩





/-! ## Actual upper-hemisphere graph for an arbitrary alternating index set -/





































































/-! ## Actual upper-hemisphere graph with self-contained alternating labels -/





































theorem actualHemisphereAlt_sigma_degree_card {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (sigma : ActualHemisphereAltChain label) :
    Fintype.card
        {rho : ActualHemisphereAltRidge label // actualHemisphereAltEdge rho sigma} =
      (simplexAltPosDeletionSet label
        (fun i : Fin (r + 1) => sigma.1.prefixChain i)).card := by
  classical
  have hcongr :=
    Fintype.card_congr (actualHemisphereAltIncidentDeletionEquiv sigma)
  have hdoor :
      Fintype.card
          {j : Fin (r + 1) //
            IsAltPos label (fun a : Fin r => sigma.1.prefixChain (j.succAbove a))} =
        (simplexAltPosDeletionSet label
          (fun i : Fin (r + 1) => sigma.1.prefixChain i)).card := by
    rw [Fintype.card_subtype]
    rfl
  exact hcongr.trans hdoor

theorem noOppositeLabelSeq_of_chain_of_noComplementary {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    (P : SignedPermutation (r + 1)) :
    NoOppositeLabelSeq (fun i : Fin (r + 1) => label (P.prefixChain i)) := by
  intro i j hcomp
  by_cases hij : i ≤ j
  · exact hno (P.prefixChain i) (P.prefixChain j) (P.prefixChain_le hij) hcomp
  · have hji : j ≤ i := le_of_not_ge hij
    have hcomp' :
        label (P.prefixChain j) = (label (P.prefixChain i)).neg := by
      apply SignedLabel.ext
      · have hp := congrArg SignedLabel.positive hcomp
        cases hi : (label (P.prefixChain i)).positive <;>
          cases hj : (label (P.prefixChain j)).positive <;>
            simp [SignedLabel.neg, hi, hj] at hp ⊢
      · have hidx := congrArg SignedLabel.index hcomp
        simpa [SignedLabel.neg] using hidx.symm
    exact hno (P.prefixChain j) (P.prefixChain i) (P.prefixChain_le hji) hcomp'

theorem actualHemisphereAlt_sigma_odd_degree_iff_top {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    (sigma : ActualHemisphereAltChain label) :
    Odd
        (Fintype.card
          {rho : ActualHemisphereAltRidge label //
            actualHemisphereAltEdge rho sigma}) ↔
      actualHemisphereAltTop sigma := by
  rw [actualHemisphereAlt_sigma_degree_card sigma, actualHemisphereAltTop]
  exact simplex_deletionParity_of_noOpposite
    (label := label) (sigma := fun i : Fin (r + 1) => sigma.1.prefixChain i)
    (noOppositeLabelSeq_of_chain_of_noComplementary hno sigma.1)

theorem actualHemisphereAltRidge_nonempty_of_boundary_odd {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hboundaryOdd :
      Odd (Fintype.card
        {rho : ActualHemisphereAltRidge label //
          actualHemisphereAltBoundary rho})) :
    Nonempty (ActualHemisphereAltRidge label) := by
  rcases hboundaryOdd with ⟨k, hk⟩
  have hpos :
      0 < Fintype.card
        {rho : ActualHemisphereAltRidge label //
          actualHemisphereAltBoundary rho} := by
    omega
  obtain ⟨rho⟩ := Fintype.card_pos_iff.mp hpos
  exact ⟨rho.1⟩



theorem ball_parity {r m : ℕ} (hr : 0 < r)
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hno : NoComplementaryComparableLabels label)
    (hboundaryOdd :
      Odd (Fintype.card
        {rho : ActualHemisphereAltRidge label //
          actualHemisphereAltBoundary rho})) :
    Odd (Fintype.card
      {sigma : ActualHemisphereAltChain label //
        actualHemisphereAltTop sigma}) := by
  classical
  let D : RhoDegreeManifoldData
      (ActualHemisphereAltRidge label) (ActualHemisphereAltChain label) :=
    actualHemisphereAltRhoDegreeData hr
      (actualHemisphereAltRidge_nonempty_of_boundary_odd hboundaryOdd)
  have hmod := D.boundary_top_parity
    (topOdd := actualHemisphereAltTop (label := label))
    (actualHemisphereAlt_sigma_odd_degree_iff_top hno)
  have hb :
      (Fintype.card
        {rho : ActualHemisphereAltRidge label //
          actualHemisphereAltBoundary rho} : ZMod 2) = 1 :=
    hboundaryOdd.natCast_zmod_two
  have hbD :
      (Fintype.card
        {rho : ActualHemisphereAltRidge label // D.boundary rho} : ZMod 2) = 1 := by
    simpa [D] using hb
  have ht :
      (Fintype.card
        {sigma : ActualHemisphereAltChain label //
          actualHemisphereAltTop sigma} : ZMod 2) = 1 := by
    simpa [hbD] using hmod.symm
  exact (ZMod.natCast_eq_one_iff_odd).mp ht











theorem equatorBoundaryAltCardBridge {r m : ℕ}
    (label : NonzeroSignedSubset (r + 1) → SignedLabel m) :
    Fintype.card
        {rho : ActualHemisphereAltRidge label //
          actualHemisphereAltBoundary rho} =
      Fintype.card (EquatorActualAltRidge (equatorRestrictedLabelOf label)) :=
  Fintype.card_congr (equatorBoundaryAltRidgeEquiv label)

/-! ## Antipodal and hemisphere bridges for self-contained alternating chains -/











































































theorem equatorActualAlt_card_eq_full_alt_pos {r m : ℕ}
    (label : NonzeroSignedSubset r → SignedLabel m) :
    Fintype.card (EquatorActualAltRidge label) =
      Fintype.card (FullAltPosChain label) :=
  Fintype.card_congr (equatorActualAltRidgeEquivFullAltPos label)







theorem upper_top_card_eq_full_alt_pos {r m : ℕ}
    {label : NonzeroSignedSubset (r + 1) → SignedLabel m}
    (hantipodal : ∀ X, label X.antipode = (label X).neg) :
    Fintype.card
        {sigma : ActualHemisphereAltChain label // actualHemisphereAltTop sigma} =
      Fintype.card (FullAltPosChain label) :=
  Fintype.card_congr (upperTopEquivFullAltPos hantipodal)





theorem fullAltPosChain_card_eq_positiveAlternatingPrefixLabelChains_one
    {m : ℕ} (label : NonzeroSignedSubset 1 → SignedLabel m) :
    Fintype.card (FullAltPosChain label) =
      (positiveAlternatingPrefixLabelChains label).card := by
  calc
    Fintype.card (FullAltPosChain label) =
        Fintype.card
          {P : SignedPermutation 1 // P ∈ positiveAlternatingPrefixLabelChains label} :=
      Fintype.card_congr
        (fullAltPosChainEquivPositiveAlternatingPrefixLabelChains_one label)
    _ = (positiveAlternatingPrefixLabelChains label).card := by
      rw [Fintype.card_subtype]
      simp

theorem fullAltPosChain_one_odd {m : ℕ} (hm : 1 ≤ m)
    {label : NonzeroSignedSubset 1 → SignedLabel m}
    (hantipodal : ∀ X, label X.antipode = (label X).neg)
    (hno : NoComplementaryComparableLabels label) :
    Odd (Fintype.card (FullAltPosChain label)) := by
  have hposOdd :=
    (kyFanParityStatement_one (m := m) hm) (by omega) hm
      label hantipodal hno
  rw [fullAltPosChain_card_eq_positiveAlternatingPrefixLabelChains_one]
  exact hposOdd

theorem fan_sphere_parity :
    ∀ r m : ℕ,
      1 ≤ r →
        r ≤ m →
          ∀ label : NonzeroSignedSubset r → SignedLabel m,
            (∀ X, label X.antipode = (label X).neg) →
              NoComplementaryComparableLabels label →
                Odd (Fintype.card (FullAltPosChain label)) := by
  intro r
  induction r with
  | zero =>
      intro m hr _hm _label _hantipodal _hno
      omega
  | succ r ih =>
      cases r with
      | zero =>
          intro m _hr hm label hantipodal hno
          exact fullAltPosChain_one_odd hm hantipodal hno
      | succ r =>
          intro m _hr hm label hantipodal hno
          let labelEq : NonzeroSignedSubset (r + 1) → SignedLabel m :=
            equatorRestrictedLabelOf label
          have heqOdd :
              Odd (Fintype.card (FullAltPosChain labelEq)) := by
            exact ih m (by omega) (by omega) labelEq
              (equatorRestrictedLabelOf_antipodal hantipodal)
              (equatorRestrictedLabelOf_noComplementary hno)
          have hboundaryOdd :
              Odd (Fintype.card
                {rho : ActualHemisphereAltRidge label //
                  actualHemisphereAltBoundary rho}) := by
            have hboundaryCard := equatorBoundaryAltCardBridge label
            have heqCard := equatorActualAlt_card_eq_full_alt_pos labelEq
            rw [hboundaryCard, heqCard]
            exact heqOdd
          have htopOdd :
              Odd (Fintype.card
                {sigma : ActualHemisphereAltChain label //
                  actualHemisphereAltTop sigma}) :=
            ball_parity (hr := by omega) hno hboundaryOdd
          rw [upper_top_card_eq_full_alt_pos hantipodal] at htopOdd
          exact htopOdd







theorem equatorActualARidge_card_eq_full_alt_pos {d : ℕ}
    (label : NonzeroSignedSubset d → SignedLabel d) :
    Fintype.card (EquatorActualARidge label) =
      Fintype.card (FullAltPosChain label) := by
  calc
    Fintype.card (EquatorActualARidge label) =
        Fintype.card (EquatorActualAltRidge label) :=
      Fintype.card_congr (equatorActualARidgeEquivEquatorActualAltRidge label)
    _ = Fintype.card (FullAltPosChain label) :=
      equatorActualAlt_card_eq_full_alt_pos label

/-! ## Fan parity induction and Tucker reduction, as explicit data interfaces -/

/-- One induction step of Ky Fan parity from the equator count and the two
degree facts.  This is the formal handshaking step; the remaining geometric
work is to instantiate `RhoDegreeManifoldData` for actual hemisphere ridges
and prove the corresponding sigma degree classifier. -/
theorem kyFan_parity_step_from_rho_sigma_data
    {R S : Type*} [Fintype R] [Fintype S]
    (D : RhoDegreeManifoldData R S)
    (topAlternating : S → Prop) [DecidablePred topAlternating]
    (hs :
      ∀ s : S,
        (Odd (Fintype.card {r : R // D.edge r s}) ↔ topAlternating s))
    (hboundary :
      Odd (Fintype.card {r : R // D.boundary r})) :
    Odd (Fintype.card {s : S // topAlternating s}) := by
  have hmod := D.boundary_top_parity topAlternating hs
  have hb : (Fintype.card {r : R // D.boundary r} : ZMod 2) = 1 :=
    hboundary.natCast_zmod_two
  have ht : (Fintype.card {s : S // topAlternating s} : ZMod 2) = 1 := by
    simpa [hb] using hmod.symm
  exact (ZMod.natCast_eq_one_iff_odd).mp ht

/-- The final reduction data from the Chapter 39 proof note: the boundary
label-set-`A` ridges are odd, rho degrees are `1/2`, and sigma degree one is
classified by the local `sigmaDoorSet` lemma above.  This theorem is deliberately
not an empty-type shortcut: it requires an explicit `Nonempty R`. -/
theorem final_reduction_from_label_set_A_graph
    {R M : Type*} [Fintype R] [Fintype M]
    (D : RhoDegreeManifoldData R M)
    (oneDoor : M → Prop) [DecidablePred oneDoor]
    (hm :
      ∀ m : M,
        (Odd (Fintype.card {r : R // D.edge r m}) ↔ oneDoor m))
    (hboundaryOdd : Odd (Fintype.card {r : R // D.boundary r})) :
    ∃ m : M, oneDoor m := by
  have hodd : Odd (Fintype.card {m : M // oneDoor m}) :=
    kyFan_parity_step_from_rho_sigma_data D oneDoor hm hboundaryOdd
  have hpos : 0 < Fintype.card {m : M // oneDoor m} := by
    rcases hodd with ⟨a, ha⟩
    omega
  obtain ⟨m⟩ := Fintype.card_pos_iff.mp hpos
  exact ⟨m.1, m.2⟩

theorem actualHemisphereA_boundary_odd_gives_prefixChain_complementary_pair {d : ℕ}
    (hd : 0 < d)
    {label : NonzeroSignedSubset (d + 1) → SignedLabel d}
    (hboundaryOdd :
      Odd (Fintype.card
        {rho : ActualHemisphereARidge label //
          actualHemisphereABoundary rho})) :
    ∃ P : SignedPermutation (d + 1), ∃ i j : Fin (d + 1), i < j ∧
      (label (P.prefixChain i)).index = (label (P.prefixChain j)).index ∧
      (label (P.prefixChain i)).positive ≠ (label (P.prefixChain j)).positive := by
  classical
  let D : RhoDegreeManifoldData
      (ActualHemisphereARidge label) (ActualHemisphereAChain label) :=
    actualHemisphereRhoDegreeData hd
      (actualHemisphereARidge_nonempty_of_boundary_odd hboundaryOdd)
  obtain ⟨sigma, hsigmaOneDoor⟩ :=
    final_reduction_from_label_set_A_graph
      (D := D)
      (oneDoor := actualHemisphereAOneDoor (label := label))
      (hm := actualHemisphereA_sigma_odd_degree_iff_oneDoor)
      hboundaryOdd
  rcases sigma.2.2 with ⟨gap, hgap⟩
  have hdoorExtra :
      SigmaDeletionHasAlternatingLabelSet
        (fun i => label (sigma.1.prefixChain i)) gap := by
    intro a
    rcases hgap a with ⟨t, ht⟩
    exact ⟨gap.succAbove t, Fin.succAbove_ne gap t, ht⟩
  have hdoorCard :
      (sigmaDoorSet (fun i => label (sigma.1.prefixChain i))).card = 1 := by
    simpa [actualHemisphereAOneDoor] using hsigmaOneDoor
  obtain ⟨i, j, hij, hidx, hsign⟩ :=
    sigmaDoorSet_card_one_gives_prefixChain_complementary_pair_of_door
      (label := label) (P := sigma.1) (extra := gap)
      hdoorExtra hdoorCard
  exact ⟨sigma.1, i, j, hij, hidx, hsign⟩





theorem equatorBoundaryCardBridge (d : ℕ) :
    EquatorBoundaryCardBridgeStatement d := by
  intro label _hantipodal _hno
  exact Fintype.card_congr (equatorBoundaryARidgeEquiv label)

theorem actualHemisphereBoundaryOdd_of_equator_card_bridge {d : ℕ}
    (hKy : KyFanUnorderedParityStatement d)
    (hbridge : EquatorBoundaryCardBridgeStatement d) :
    ActualHemisphereBoundaryOddStatement d := by
  intro label hantipodal hno
  have hodd :=
    equatorRestrictedLabel_unordered_odd hKy hantipodal hno
  have hcard := hbridge label hantipodal hno
  simpa [hcard] using hodd

theorem tuckerLemmaStatement_succ_of_actualHemisphere_boundary_odd {d : ℕ}
    (hd : 0 < d)
    (hboundaryOdd : ActualHemisphereBoundaryOddStatement d) :
    TuckerLemmaStatement (d + 1) := by
  apply tuckerLemmaStatement_of_chain_complementary_of_no_complementary
  intro label hantipodal hno
  exact actualHemisphereA_boundary_odd_gives_prefixChain_complementary_pair hd
    (hboundaryOdd label hantipodal hno)

theorem tuckerLemmaStatement_succ_of_equator_boundary_card_bridge {d : ℕ}
    (hd : 1 ≤ d) (hKy : KyFanUnorderedParityStatement d)
    (hbridge : EquatorBoundaryCardBridgeStatement d) :
    TuckerLemmaStatement (d + 1) :=
  tuckerLemmaStatement_succ_of_actualHemisphere_boundary_odd hd
    (actualHemisphereBoundaryOdd_of_equator_card_bridge hKy hbridge)

theorem tuckerLemma_pos_of_kyFanUnordered
    (hKy : ∀ d : ℕ, 1 ≤ d → KyFanUnorderedParityStatement d) :
    ∀ n : ℕ, 1 ≤ n → TuckerLemmaStatement n := by
  intro n hn
  cases n with
  | zero =>
      omega
  | succ d =>
      cases d with
      | zero =>
          exact tuckerLemmaStatement_one
      | succ e =>
          exact tuckerLemmaStatement_succ_of_equator_boundary_card_bridge
            (d := e + 1) (by omega) (hKy (e + 1) (by omega))
            (equatorBoundaryCardBridge (e + 1))

theorem kyFanUnordered_all :
    ∀ d : ℕ, 1 ≤ d → KyFanUnorderedParityStatement d := by
  intro d hd label hantipodal hno
  have hfull :
      Odd (Fintype.card (FullAltPosChain label)) :=
    fan_sphere_parity d d hd le_rfl label hantipodal hno
  rw [equatorActualARidge_card_eq_full_alt_pos label]
  exact hfull

theorem tuckerLemma_pos :
    ∀ n : ℕ, 1 ≤ n → TuckerLemmaStatement n :=
  tuckerLemma_pos_of_kyFanUnordered kyFanUnordered_all







end ProofsInTheBook.Chapter39

end


set_option autoImplicit true
open ProofsInTheBook.Chapter39
open SignedPermutation

theorem solution {n k : ℕ} (hk : 1 ≤ k) (hn : 2 * k ≤ n) :
    (∃ C : KneserVertex n k → Fin (n - 2 * k + 2),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) ∧
    (¬ ∃ C : KneserVertex n k → Fin (n - 2 * k + 1),
        ∀ a b, (kneserGraph n k).Adj a b → C a ≠ C b) :=
  chapter39 hk hn (tuckerLemma_pos n (by omega))
