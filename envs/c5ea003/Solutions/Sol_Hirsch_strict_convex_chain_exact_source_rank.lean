-- Prove2me | solution 1 for Hirsch.strict_convex_chain_exact_source_rank
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-23T19:58:40.411501+00:00
-- url     : https://prove2.me/submissions/a2f3ea44-ec31-41a9-a4da-d3929d79340c

import Mathlib

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Hirsch.ConvexChainRank

variable {n : ℕ}

def StrictChain (w a : Fin (n+1) → ℝ) : Prop :=
  ∀ i j k, i<j → j<k →
    (a j-a i)*(w k-w j) < (a k-a j)*(w j-w i)

noncomputable def above (f : Fin (n+1) → ℝ) (k : Fin (n+1)) : Finset ℝ := by
  classical
  exact (Finset.univ.image f).filter (fun z => f k<z)

noncomputable def below (f : Fin (n+1) → ℝ) (k : Fin (n+1)) : Finset ℝ := by
  classical
  exact (insert 0 (Finset.univ.image (fun i => 1/f i))).filter (fun z => z<1/f k)

/-- Tilting preserves every strict secant-slope inequality. -/
lemma tilt_chain (w a : Fin (n+1) → ℝ) (ha : StrictChain w a) (t : ℝ) :
    StrictChain w (fun i => a i+t*w i) := by
  intro i j k hij hjk
  have h := ha i j k hij hjk
  nlinarith

lemma left_step (w f : Fin (n+1) → ℝ) (hw : StrictMono w)
    (hf : StrictChain w f) (i j k : Fin (n+1))
    (hij : i<j) (hjk : j<k) (hdown : f k ≤ f j) : f j<f i := by
  have h := hf i j k hij hjk
  have hp : 0<w k-w j := sub_pos.mpr (hw hjk)
  have hq : 0<w j-w i := sub_pos.mpr (hw hij)
  have hr : (f k-f j)*(w j-w i) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hdown) hq.le
  by_contra hn
  have hz : 0 ≤ (f j-f i)*(w k-w j) :=
    mul_nonneg (sub_nonneg.mpr (le_of_not_gt hn)) hp.le
  linarith

lemma right_step (w f : Fin (n+1) → ℝ) (hw : StrictMono w)
    (hf : StrictChain w f) (i j k : Fin (n+1))
    (hij : i<j) (hjk : j<k) (hup : f i ≤ f j) : f j<f k := by
  have h := hf i j k hij hjk
  have hp : 0<w k-w j := sub_pos.mpr (hw hjk)
  have hq : 0<w j-w i := sub_pos.mpr (hw hij)
  have hl : 0 ≤ (f j-f i)*(w k-w j) :=
    mul_nonneg (sub_nonneg.mpr hup) hp.le
  by_contra hn
  have hz : (f k-f j)*(w j-w i) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt hn)) hq.le
  linarith

/-- Every tilt has an entire strictly ordered side above the source.
This counts DISTINCT levels, even when the two sides have coincidences. -/
theorem rank_lower_bound (w f : Fin (n+1) → ℝ) (hw : StrictMono w)
    (hf : StrictChain w f) (k : Fin (n+1)) :
    min k.val (n-k.val) ≤ (above f k).card := by
  classical
  by_cases hk : k.val=0
  · simp only [hk,Nat.zero_min]
    exact Nat.zero_le _
  let p : Fin (n+1) := ⟨k.val-1,by have h := k.isLt; omega⟩
  have hpk : p<k := by change k.val-1<k.val; omega
  by_cases hdown : f k<f p
  · have hside : ∀ i : Fin (n+1), i<k → f k<f i := by
      intro i hik
      by_cases hip : i=p
      · simpa only [hip] using hdown
      · have hil : i<p := by
          have hv : i.val<k.val := hik
          have hne : i.val ≠ p.val := fun h => hip (Fin.ext h)
          change i.val<k.val-1
          dsimp [p] at hne
          omega
        exact hdown.trans (left_step w f hw hf i p k hil hpk hdown.le)
    have hinj : Set.InjOn f (Finset.Iio k : Set (Fin (n+1))) := by
      intro i hi j hj he
      have hik : i<k := Finset.mem_Iio.mp hi
      have hjk : j<k := Finset.mem_Iio.mp hj
      rcases lt_trichotomy i j with hij | hij | hji
      · exact False.elim ((ne_of_lt (left_step w f hw hf i j k hij hjk
          (hside j hjk).le)) he.symm)
      · exact hij
      · exact False.elim ((ne_of_lt (left_step w f hw hf j i k hji hik
          (hside i hik).le)) he)
    have hsub : (Finset.Iio k).image f ⊆ above f k := by
      intro z hz
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
        ⟨i,Finset.mem_univ _,rfl⟩,hside i (Finset.mem_Iio.mp hi)⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj,Fin.card_Iio] at hc
    exact (min_le_left _ _).trans hc
  · have hup : f p ≤ f k := le_of_not_gt hdown
    have hside : ∀ j : Fin (n+1), k<j → f k<f j := by
      intro j hkj
      exact right_step w f hw hf p k j hpk hkj hup
    have hinj : Set.InjOn f (Finset.Ioi k : Set (Fin (n+1))) := by
      intro i hi j hj he
      have hki : k < i := Finset.mem_Ioi.mp hi
      have hkj : k<j := Finset.mem_Ioi.mp hj
      rcases lt_trichotomy i j with hij | hij | hji
      · exact False.elim ((ne_of_lt (right_step w f hw hf k i j hki hij
          (hside i hki).le)) he)
      · exact hij
      · exact False.elim ((ne_of_lt (right_step w f hw hf k j i hkj hji
          (hside j hkj).le)) he.symm)
    have hsub : (Finset.Ioi k).image f ⊆ above f k := by
      intro z hz
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
        ⟨i,Finset.mem_univ _,rfl⟩,hside i (Finset.mem_Ioi.mp hi)⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj,Fin.card_Ioi] at hc
    have hc' : n-k.val ≤ (above f k).card := by simpa using hc
    exact (min_le_right _ _).trans hc'

/-- Two source-independent extreme tilts make all heights monotone.
The tilt size is derived from a finite maximum, not given as an oracle. -/
theorem extreme_tilts (w a : Fin (n+1) → ℝ) (hw : StrictMono w) :
    ∃ M : ℝ, 0<M ∧ StrictMono (fun i => a i+M*w i) ∧
      StrictAnti (fun i => a i+(-M)*w i) := by
  classical
  let B := fun p : Fin (n+1) × Fin (n+1) =>
    |(a p.2-a p.1)/(w p.2-w p.1)|
  obtain ⟨p,hp,hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin (n+1) × Fin (n+1))) B
    ⟨(0,0),Finset.mem_univ _⟩
  let M : ℝ := B p+1
  have hM : 0<M := by dsimp [M,B]; positivity
  have hb : ∀ i j : Fin (n+1), i<j → |a j-a i|<M*(w j-w i) := by
    intro i j hij
    have hwpos : 0<w j-w i := sub_pos.mpr (hw hij)
    have hbound := hmax (i,j) (Finset.mem_univ _)
    have hdiv : |a j-a i|/(w j-w i) ≤ B p := by
      simpa only [B,abs_div,abs_of_pos hwpos] using hbound
    have hlt : |a j-a i|/(w j-w i)<M := by dsimp [M]; linarith
    exact (div_lt_iff₀ hwpos).mp hlt
  refine ⟨M,hM,?_,?_⟩
  · intro i j hij
    have hh := hb i j hij
    have hl := neg_abs_le (a j-a i)
    nlinarith
  · intro i j hij
    have hh := hb i j hij
    have hu := le_abs_self (a j-a i)
    nlinarith

lemma above_mono (f : Fin (n+1) → ℝ) (hf : StrictMono f) (k : Fin (n+1)) :
    (above f k).card=n-k.val := by
  classical
  have he : above f k=(Finset.Ioi k).image f := by
    ext z
    constructor
    · intro hz
      obtain ⟨hi,hl⟩ := Finset.mem_filter.mp hz
      obtain ⟨i,hu,rfl⟩ := Finset.mem_image.mp hi
      have hki : k < i := by
        by_contra hn
        exact (not_le_of_gt hl) (hf.monotone (le_of_not_gt hn))
      exact Finset.mem_image.mpr ⟨i,Finset.mem_Ioi.mpr hki,rfl⟩
    · intro hz
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
        ⟨i,Finset.mem_univ _,rfl⟩,hf (Finset.mem_Ioi.mp hi)⟩
  rw [he,Finset.card_image_of_injective _ hf.injective,Fin.card_Ioi]
  omega

lemma above_anti (f : Fin (n+1) → ℝ) (hf : StrictAnti f) (k : Fin (n+1)) :
    (above f k).card=k.val := by
  classical
  have he : above f k=(Finset.Iio k).image f := by
    ext z
    constructor
    · intro hz
      obtain ⟨hi,hl⟩ := Finset.mem_filter.mp hz
      obtain ⟨i,hu,rfl⟩ := Finset.mem_image.mp hi
      have hik : i<k := by
        by_contra hn
        exact (not_le_of_gt hl) (hf.antitone (le_of_not_gt hn))
      exact Finset.mem_image.mpr ⟨i,Finset.mem_Iio.mpr hik,rfl⟩
    · intro hz
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
        ⟨i,Finset.mem_univ _,rfl⟩,hf (Finset.mem_Iio.mp hi)⟩
  rw [he,Finset.card_image_of_injective _ hf.injective,Fin.card_Iio]

lemma translate_card (f : Fin (n+1) → ℝ) (k : Fin (n+1)) (c : ℝ) :
    (above (fun i => f i+c) k).card=(above f k).card := by
  classical
  have he : above (fun i => f i+c) k=(above f k).image (fun z => z+c) := by
    ext z
    constructor
    · intro hz
      obtain ⟨hi,hl⟩ := Finset.mem_filter.mp hz
      obtain ⟨i,hu,rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_image.mpr ⟨f i,Finset.mem_filter.mpr
        ⟨Finset.mem_image.mpr ⟨i,hu,rfl⟩,by linarith⟩,rfl⟩
    · intro hz
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hi,hl⟩ := Finset.mem_filter.mp hb
      obtain ⟨i,hu,rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i,hu,rfl⟩,by linarith⟩
  rw [he]
  exact Finset.card_image_of_injective _ (fun a b hab => add_right_cancel hab)

lemma positive_translate (f : Fin (n+1) → ℝ) : ∃ c : ℝ, ∀ i, 0<f i+c := by
  obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin (n+1)))
    f ⟨0,Finset.mem_univ _⟩
  refine ⟨1-f j,?_⟩
  intro i
  have hi := hmin i (Finset.mem_univ _)
  linarith

/-- Positive reciprocation reverses order; target zero adds exactly one level. -/
lemma reciprocal_card (f : Fin (n+1) → ℝ) (hf : ∀ i, 0<f i) (k : Fin (n+1)) :
    (below f k).card=(above f k).card+1 := by
  classical
  have horder : ∀ i, 1/f i<1/f k ↔ f k<f i := by
    intro i
    rw [div_lt_div_iff₀ (hf i) (hf k)]
    simp only [one_mul]
  have he : below f k=insert 0 ((above f k).image (fun z => 1/z)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨hi,hl⟩ := Finset.mem_filter.mp hz
      rcases Finset.mem_insert.mp hi with hz0 | hzI
      · exact Finset.mem_insert.mpr (Or.inl hz0)
      · obtain ⟨i,hu,rfl⟩ := Finset.mem_image.mp hzI
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr
          ⟨f i,Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i,hu,rfl⟩,
            (horder i).mp hl⟩,rfl⟩))
    · intro hz
      rcases Finset.mem_insert.mp hz with hz0 | hzI
      · subst z
        exact Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _,
          div_pos (by norm_num) (hf k)⟩
      · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hzI
        obtain ⟨hi,hl⟩ := Finset.mem_filter.mp hb
        obtain ⟨i,hu,rfl⟩ := Finset.mem_image.mp hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem
          (Finset.mem_image.mpr ⟨i,hu,rfl⟩),(horder i).mpr hl⟩
  have hn : (0:ℝ) ∉ (above f k).image (fun z => 1/z) := by
    intro hz
    obtain ⟨b,hb,heq⟩ := Finset.mem_image.mp hz
    obtain ⟨hi,hl⟩ := Finset.mem_filter.mp hb
    obtain ⟨i,hu,rfl⟩ := Finset.mem_image.mp hi
    exact (ne_of_gt (div_pos (by norm_num : (0:ℝ)<1) (hf i))) heq
  have hinj : Function.Injective (fun z : ℝ => 1/z) := by
    intro a b hab
    have hh := congrArg (fun z : ℝ => z⁻¹) hab
    simpa only [one_div,inv_inv] using hh
  rw [he,Finset.card_insert_of_notMem hn,Finset.card_image_of_injective _ hinj]

/-- Exact optimization, not a finite guessed list of slopes or a rank hypothesis. -/
theorem exact_rank (w a : Fin (n+1) → ℝ) (hw : StrictMono w)
    (ha : StrictChain w a) :
    ∃ M : ℝ, 0<M ∧ ∀ k : Fin (n+1),
      (∀ t : ℝ, min k.val (n-k.val) ≤ (above (fun i => a i+t*w i) k).card) ∧
      (above (fun i => a i+(-M)*w i) k).card=k.val ∧
      (above (fun i => a i+M*w i) k).card=n-k.val ∧
      ∃ t c : ℝ, (t=M ∨ t=-M) ∧ (∀ i, 0<a i+t*w i+c) ∧
        (above (fun i => a i+t*w i+c) k).card=min k.val (n-k.val) ∧
        (below (fun i => a i+t*w i+c) k).card=min k.val (n-k.val)+1 ∧
        2*(below (fun i => a i+t*w i+c) k).card ≤ n+2 := by
  classical
  obtain ⟨M,hM,hmono,hanti⟩ := extreme_tilts w a hw
  refine ⟨M,hM,?_⟩
  intro k
  have hl := above_anti _ hanti k
  have hr := above_mono _ hmono k
  have he : ∃ t : ℝ, (t=M ∨ t=-M) ∧
      (above (fun i => a i+t*w i) k).card=min k.val (n-k.val) := by
    by_cases hk : k.val ≤ n-k.val
    · exact ⟨-M,Or.inr rfl,by rw [hl,min_eq_left hk]⟩
    · exact ⟨M,Or.inl rfl,by rw [hr,min_eq_right (by omega : n-k.val ≤ k.val)]⟩
  obtain ⟨t,ht,hval⟩ := he
  obtain ⟨c,hc⟩ := positive_translate (fun i => a i+t*w i)
  have hcval : (above (fun i => a i+t*w i+c) k).card=min k.val (n-k.val) :=
    (translate_card (fun i => a i+t*w i) k c).trans hval
  have hbval : (below (fun i => a i+t*w i+c) k).card=min k.val (n-k.val)+1 := by
    rw [reciprocal_card _ hc k,hcval]
  refine ⟨(fun t => rank_lower_bound w _ hw (tilt_chain w a ha t) k),hl,hr,
    t,c,ht,hc,hcval,hbval,?_⟩
  rw [hbval]
  have hk := k.isLt
  have hleft := min_le_left k.val (n-k.val)
  have hright := min_le_right k.val (n-k.val)
  omega

end Hirsch.ConvexChainRank

/-- A strict convex inverse-height chain has an exact closed-form optimum. -/
theorem solution (n : ℕ) (w a : Fin (n+1) → ℝ)
    (hw : StrictMono w)
    (ha : ∀ i j k : Fin (n+1), i<j → j<k →
      (a j-a i)*(w k-w j) < (a k-a j)*(w j-w i)) :
    let U := fun (t : ℝ) (k : Fin (n+1)) =>
      @Finset.filter ℝ (fun z => a k+t*w k<z) (fun _ => Classical.propDecidable _)
        (Finset.univ.image (fun i => a i+t*w i))
    let B := fun (t c : ℝ) (k : Fin (n+1)) =>
      @Finset.filter ℝ (fun z => z<1/(a k+t*w k+c)) (fun _ => Classical.propDecidable _)
        (insert 0 (Finset.univ.image (fun i => 1/(a i+t*w i+c))))
    ∃ M : ℝ, 0<M ∧ ∀ k : Fin (n+1),
      (∀ t : ℝ, min k.val (n-k.val) ≤ (U t k).card) ∧
      (U (-M) k).card=k.val ∧ (U M k).card=n-k.val ∧
      ∃ t c : ℝ, (t=M ∨ t=-M) ∧ (∀ i, 0<a i+t*w i+c) ∧
        (U t k).card=min k.val (n-k.val) ∧
        (B t c k).card=min k.val (n-k.val)+1 ∧
        2*(B t c k).card ≤ n+2 := by
  classical
  let U := fun (t : ℝ) (k : Fin (n+1)) =>
    @Finset.filter ℝ (fun z => a k+t*w k<z) (fun _ => Classical.propDecidable _)
      (Finset.univ.image (fun i => a i+t*w i))
  let B := fun (t c : ℝ) (k : Fin (n+1)) =>
    @Finset.filter ℝ (fun z => z<1/(a k+t*w k+c)) (fun _ => Classical.propDecidable _)
      (insert 0 (Finset.univ.image (fun i => 1/(a i+t*w i+c))))
  have hU : ∀ t k, Hirsch.ConvexChainRank.above (fun i => a i+t*w i) k=U t k := by
    intro t k
    ext z
    simp only [Hirsch.ConvexChainRank.above,U,Finset.mem_filter,Finset.mem_image]
  have hB : ∀ t c k, Hirsch.ConvexChainRank.below (fun i => a i+t*w i+c) k=B t c k := by
    intro t c k
    ext z
    simp only [Hirsch.ConvexChainRank.below,B,Finset.mem_filter,Finset.mem_insert,
      Finset.mem_image]
  obtain ⟨M,hM,hall⟩ := Hirsch.ConvexChainRank.exact_rank w a hw ha
  refine ⟨M,hM,?_⟩
  intro k
  obtain ⟨hlo,hl,hr,t,c,ht,hc,hshift,hb,hbound⟩ := hall k
  have hval : (U t k).card=min k.val (n-k.val) := by
    have hbase := (Hirsch.ConvexChainRank.translate_card (fun i => a i+t*w i) k c).symm.trans hshift
    simpa only [hU] using hbase
  refine ⟨?_,?_,?_,t,c,ht,hc,hval,?_,?_⟩
  · simpa only [hU] using hlo
  · simpa only [hU] using hl
  · simpa only [hU] using hr
  · simpa only [hB] using hb
  · simpa only [hB] using hbound

#print axioms Hirsch.ConvexChainRank.tilt_chain
#print axioms Hirsch.ConvexChainRank.rank_lower_bound
#print axioms Hirsch.ConvexChainRank.extreme_tilts
#print axioms Hirsch.ConvexChainRank.reciprocal_card
#print axioms Hirsch.ConvexChainRank.exact_rank
#print axioms solution
