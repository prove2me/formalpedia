-- Prove2me | solution 1 for Hirsch.actual_planar_vertices_rank_attaining_original_routes
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-23T21:46:41.772544+00:00
-- url     : https://prove2.me/submissions/3a286319-58d8-4f66-9222-c8a7da9669b9

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

namespace Hirsch.HullCoordinate
open Set
variable {d : ℕ}

/-- Equality in an upper support bound uses only maximizing generators.
The target K may be any convex set, not a supplied face or edge. -/
lemma hull_support (C : Finset (Fin d → ℝ)) (f : (Fin d → ℝ) →ₗ[ℝ] ℝ)
    (M : ℝ) (K : Set (Fin d → ℝ)) (hK : Convex ℝ K)
    (hC : ∀ x ∈ C, f x ≤ M ∧ (f x=M → x ∈ K)) :
    ∀ x ∈ convexHull ℝ (C : Set (Fin d → ℝ)),
      f x ≤ M ∧ (f x=M → x ∈ K) := by
  apply convexHull_min hC
  intro x hx y hy a b ha hb hab
  change f (a • x+b • y) ≤ M ∧ (f (a • x+b • y)=M → a • x+b • y ∈ K)
  have hval : f (a • x+b • y)=a*f x+b*f y := by
    simp only [map_add, map_smul, smul_eq_mul]
  constructor
  · rw [hval]
    calc
      a*f x+b*f y ≤ a*M+b*M := add_le_add
        (mul_le_mul_of_nonneg_left hx.1 ha) (mul_le_mul_of_nonneg_left hy.1 hb)
      _ = M := by rw [← add_mul, hab, one_mul]
  · intro he
    by_cases ha0 : a=0
    · have hb1 : b=1 := by linarith
      have hyM : f y=M := by simpa [ha0, hb1] using he
      simpa [ha0, hb1] using hy.2 hyM
    by_cases hb0 : b=0
    · have ha1 : a=1 := by linarith
      have hxM : f x=M := by simpa [ha1, hb0] using he
      simpa [ha1, hb0] using hx.2 hxM
    have hsum : a*(M-f x)+b*(M-f y)=0 := by
      calc
        a*(M-f x)+b*(M-f y) = (a+b)*M-(a*f x+b*f y) := by ring
        _ = 0 := by rw [hab, one_mul, ← hval, he, sub_self]
    have hax := mul_nonneg ha (sub_nonneg.mpr hx.1)
    have hby := mul_nonneg hb (sub_nonneg.mpr hy.1)
    have hax0 : a*(M-f x)=0 := by linarith
    have hby0 : b*(M-f y)=0 := by linarith
    have hxM : f x=M :=
      (sub_eq_zero.mp ((mul_eq_zero.mp hax0).resolve_left ha0)).symm
    have hyM : f y=M :=
      (sub_eq_zero.mp ((mul_eq_zero.mp hby0).resolve_left hb0)).symm
    exact hK (hx.2 hxM) (hy.2 hyM) ha hb hab


end Hirsch.HullCoordinate

namespace Hirsch.RadialPolygon

open Set

abbrev Point := Fin 2 → ℝ
abbrev Form := Point →ₗ[ℝ] ℝ

/-- An actual extreme point cannot be a subconvex radial combination of
three other feasible points. No planar or finite-hull hypothesis is needed. -/
lemma radial_mass_gt_one {d : ℕ} (P : Set (Fin d → ℝ)) (hP : Convex ℝ P)
    (v u x y : Fin d → ℝ) (hv : v ∈ P) (hu : u ∈ P) (hy : y ∈ P)
    (hx : x ∈ P.extremePoints ℝ) (hvx : v ≠ x) (hux : u ≠ x) (hyx : y ≠ x)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (heq : x-v = r • (u-v)+s • (y-v)) : 1 < r+s := by
  classical
  by_contra hn
  have hrs : r+s ≤ 1 := le_of_not_gt hn
  have hc : Convex ℝ (P \ {x}) := (hP.mem_extremePoints_iff_convex_diff.mp hx).2
  let c : Fin 3 → ℝ := ![1-r-s,r,s]
  let q : Fin 3 → (Fin d → ℝ) := ![v,u,y]
  have hnon : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ c i := by
    intro i hi
    fin_cases i <;> simp [c] <;> linarith
  have hone : ∑ i : Fin 3, c i = 1 := by
    simp [Fin.sum_univ_succ,c]
    <;> ring
  have hmem : ∀ i ∈ (Finset.univ : Finset (Fin 3)), q i ∈ P \ {x} := by
    intro i hi
    fin_cases i
    · exact ⟨hv,hvx⟩
    · exact ⟨hu,hux⟩
    · exact ⟨hy,hyx⟩
  have hm := hc.sum_mem hnon hone hmem
  have hid : (∑ i : Fin 3, c i • q i) = x := by
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    change (1-r-s) • v+(r • u+s • y)=x
    calc
      (1-r-s) • v+(r • u+s • y) = v+(r • (u-v)+s • (y-v)) := by module
      _ = x := by rw [← heq]; abel
  rw [hid] at hm
  exact hm.2 rfl

/-- Two independent linear coordinates recover the normalized original vector. -/
lemma normalized_interpolation (h e : Form)
    (hinj : Function.Injective (fun z : Point => (h z,e z)))
    (v u x y : Point) (hu : 0 < h (u-v)) (hx : 0 < h (x-v)) (hy : 0 < h (y-v))
    (r s : ℝ) (hrs : r+s=1)
    (hw : r*(e (u-v)/h (u-v))+s*(e (y-v)/h (y-v))=e (x-v)/h (x-v)) :
    (1/h (x-v)) • (x-v) =
      r • ((1/h (u-v)) • (u-v))+s • ((1/h (y-v)) • (y-v)) := by
  apply hinj
  apply Prod.ext
  · change h ((1/h (x-v)) • (x-v)) =
      h (r • ((1/h (u-v)) • (u-v))+s • ((1/h (y-v)) • (y-v)))
    simp only [map_add,map_smul,smul_eq_mul]
    rw [div_mul_cancel₀ _ (ne_of_gt hx),div_mul_cancel₀ _ (ne_of_gt hu),
      div_mul_cancel₀ _ (ne_of_gt hy),mul_one,mul_one,hrs]
  · change e ((1/h (x-v)) • (x-v)) =
      e (r • ((1/h (u-v)) • (u-v))+s • ((1/h (y-v)) • (y-v)))
    simpa only [map_add,map_smul,smul_eq_mul,one_div,div_eq_mul_inv,one_mul,mul_comm] using hw.symm

/-- Extremality forces the inverse-height point strictly below every chord
between original vertices whose normalized horizontal coordinates bracket it. -/
theorem strict_chord (P : Set Point) (hP : Convex ℝ P) (h e : Form)
    (hinj : Function.Injective (fun z : Point => (h z,e z)))
    (v u x y : Point) (hv : v ∈ P) (huP : u ∈ P) (hyP : y ∈ P)
    (hxP : x ∈ P.extremePoints ℝ) (hvx : v ≠ x) (hux : u ≠ x) (hyx : y ≠ x)
    (hu : 0 < h (u-v)) (hx : 0 < h (x-v)) (hy : 0 < h (y-v))
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r+s=1)
    (hw : r*(e (u-v)/h (u-v))+s*(e (y-v)/h (y-v))=e (x-v)/h (x-v)) :
    1/h (x-v) < r*(1/h (u-v))+s*(1/h (y-v)) := by
  have hi := normalized_interpolation h e hinj v u x y hu hx hy r s hrs hw
  have heq : x-v = (h (x-v)*r*(1/h (u-v))) • (u-v)+
      (h (x-v)*s*(1/h (y-v))) • (y-v) := by
    calc
      x-v = h (x-v) • ((1/h (x-v)) • (x-v)) := by
        rw [smul_smul]
        have hh : h (x-v)*(1/h (x-v))=1 := by
          rw [mul_comm]; exact div_mul_cancel₀ _ (ne_of_gt hx)
        rw [hh,one_smul]
      _ = _ := by rw [hi,smul_add]; simp only [smul_smul,mul_assoc]
  have hm := radial_mass_gt_one P hP v u x y hv huP hyP hxP hvx hux hyx
    (h (x-v)*r*(1/h (u-v))) (h (x-v)*s*(1/h (y-v)))
    (by positivity) (by positivity) heq
  apply (div_lt_iff₀ hx).2
  nlinarith

/-- Strict chain convexity is DERIVED from original vertex extremality. -/
theorem vertex_chain {n : ℕ} (P : Set Point) (hP : Convex ℝ P)
    (v : Point) (p : Fin (n+1) → Point) (h e : Form)
    (hv : v ∈ P) (hp : ∀ i, p i ∈ P.extremePoints ℝ)
    (hpos : ∀ i, 0 < h (p i-v))
    (hinj : Function.Injective (fun z : Point => (h z,e z)))
    (hw : StrictMono (fun i => e (p i-v)/h (p i-v))) :
    Hirsch.ConvexChainRank.StrictChain
      (fun i => e (p i-v)/h (p i-v)) (fun i => 1/h (p i-v)) := by
  intro i j k hij hjk
  let w := fun q => e (p q-v)/h (p q-v)
  let a := fun q => 1/h (p q-v)
  have hijw : w i < w j := hw hij
  have hjkw : w j < w k := hw hjk
  let q := w k-w i
  have hq : 0 < q := by dsimp [q]; linarith
  let r := (w k-w j)/q
  let s := (w j-w i)/q
  have hr : 0 ≤ r := (div_pos (sub_pos.mpr hjkw) hq).le
  have hs : 0 ≤ s := (div_pos (sub_pos.mpr hijw) hq).le
  have hrq : r*q=w k-w j := div_mul_cancel₀ _ (ne_of_gt hq)
  have hsq : s*q=w j-w i := div_mul_cancel₀ _ (ne_of_gt hq)
  have hrs : r+s=1 := by
    apply (mul_right_cancel₀ (ne_of_gt hq))
    dsimp [q] at *
    nlinarith
  have hw' : r*w i+s*w k=w j := by
    apply (mul_right_cancel₀ (ne_of_gt hq))
    calc
      (r*w i+s*w k)*q = w i*(r*q)+w k*(s*q) := by ring
      _ = w j*q := by rw [hrq,hsq]; dsimp [q]; ring
  have hvj : v ≠ p j := by
    intro he
    have hz := hpos j
    rw [← he,sub_self,map_zero] at hz
    exact (lt_irrefl _) hz
  have hijp : p i ≠ p j := by
    intro he
    have hwne := ne_of_lt hijw
    apply hwne
    simp only [w,he]
  have hkjp : p k ≠ p j := by
    intro he
    have hwne := ne_of_gt hjkw
    apply hwne
    simp only [w,he]
  have hc : a j < r*a i+s*a k := strict_chord P hP h e hinj
    v (p i) (p j) (p k) hv (hp i).1 (hp k).1 (hp j) hvj hijp hkjp
    (hpos i) (hpos j) (hpos k) r s hr hs hrs hw'
  have hm := mul_lt_mul_of_pos_right hc hq
  have he : (r*a i+s*a k)*q=a i*(w k-w j)+a k*(w j-w i) := by
    calc
      _ = a i*(r*q)+a k*(s*q) := by ring
      _ = _ := by rw [hrq,hsq]
  rw [he] at hm
  change (a j-a i)*(w k-w j) < (a k-a j)*(w j-w i)
  dsimp [q] at hm
  nlinarith

/-- A secant through consecutive chain vertices is strictly below every other
chain vertex. This is the complete support test, including both sides. -/
lemma consecutive_secant {n : ℕ} (w a : Fin (n+1) → ℝ) (hw : StrictMono w)
    (ha : Hirsch.ConvexChainRank.StrictChain w a) (j : Fin n) :
    ∃ s t : ℝ,
      s*w j.castSucc+t=a j.castSucc ∧ s*w j.succ+t=a j.succ ∧
      ∀ i, s*w i+t ≤ a i ∧
        (s*w i+t=a i → i=j.castSucc ∨ i=j.succ) := by
  let u := j.castSucc
  let v := j.succ
  have huv : u < v := by change j.val < j.val+1; omega
  have hd : 0 < w v-w u := sub_pos.mpr (hw huv)
  let s := (a v-a u)/(w v-w u)
  let t := a u-s*w u
  have hs : s*(w v-w u)=a v-a u := div_mul_cancel₀ _ (ne_of_gt hd)
  have hleft : s*w u+t=a u := by dsimp [t]; ring
  have hright : s*w v+t=a v := by dsimp [t]; nlinarith
  refine ⟨s,t,hleft,hright,?_⟩
  intro i
  by_cases hiu : i=u
  · subst i
    exact ⟨hleft.le,fun _ => Or.inl rfl⟩
  by_cases hiv : i=v
  · subst i
    exact ⟨hright.le,fun _ => Or.inr rfl⟩
  have hcases : i < u ∨ v < i := by
    have hne1 : i.val ≠ j.val := fun he => hiu (Fin.ext he)
    have hne2 : i.val ≠ j.val+1 := fun he => hiv (Fin.ext he)
    change i.val < j.val ∨ j.val+1 < i.val
    omega
  have hstrict : s*w i+t < a i := by
    rcases hcases with hi | hi
    · have hc := ha i u v hi huv
      have hid : (a u-a i)*(w v-w u)-(a v-a u)*(w u-w i) =
          (s*w i+t-a i)*(w v-w u) := by
        calc
          _ = (a u-a i)*(w v-w u)-(s*(w v-w u))*(w u-w i) := by rw [hs]
          _ = _ := by dsimp [t]; ring
      have hprod : (s*w i+t-a i)*(w v-w u) < 0 := by
        rw [← hid]
        exact sub_neg.mpr hc
      have hneg : s*w i+t-a i < 0 := by
        by_contra hn
        have hz := mul_nonneg (le_of_not_gt hn) hd.le
        linarith
      linarith
    · have hc := ha u v i huv hi
      have hid : (a v-a u)*(w i-w v)-(a i-a v)*(w v-w u) =
          (s*w i+t-a i)*(w v-w u) := by
        calc
          _ = (s*(w v-w u))*(w i-w v)-(a i-(s*w v+t))*(w v-w u) := by rw [hs,hright]
          _ = _ := by ring
      have hprod : (s*w i+t-a i)*(w v-w u) < 0 := by
        rw [← hid]
        exact sub_neg.mpr hc
      have hneg : s*w i+t-a i < 0 := by
        by_contra hn
        have hz := mul_nonneg (le_of_not_gt hn) hd.le
        linarith
      linarith
  exact ⟨hstrict.le,fun he => False.elim ((ne_of_lt hstrict) he)⟩

end Hirsch.RadialPolygon
namespace Hirsch.RadialPolygon

open Set

/-- Exact finite-generator support gives the WHOLE original exposed segment. -/
lemma exposed_segment (C : Finset Point) (u y : Point) (hu : u ∈ C) (hy : y ∈ C)
    (f : Form) (hfy : f y=f u)
    (hC : ∀ z ∈ C, f z ≤ f u ∧ (f z=f u → z=u ∨ z=y)) :
    IsExposed ℝ (convexHull ℝ (C : Set Point)) (segment ℝ u y) := by
  have huP : u ∈ convexHull ℝ (C : Set Point) := subset_convexHull ℝ _ hu
  have hyP : y ∈ convexHull ℝ (C : Set Point) := subset_convexHull ℝ _ hy
  have hc : ∀ z ∈ C, f z ≤ f u ∧ (f z=f u → z ∈ segment ℝ u y) := by
    intro z hz
    refine ⟨(hC z hz).1,?_⟩
    intro he
    rcases (hC z hz).2 he with he | he
    · rw [he]; exact left_mem_segment ℝ _ _
    · rw [he]; exact right_mem_segment ℝ _ _
  have hs := Hirsch.HullCoordinate.hull_support C f (f u) (segment ℝ u y)
    (convex_segment u y) hc
  intro _
  refine ⟨f.toContinuousLinearMap,?_⟩
  ext z
  constructor
  · intro hz
    obtain ⟨a,b,ha,hb,hab,he⟩ := hz
    have hzP := he ▸ (convex_convexHull ℝ (C : Set Point)) huP hyP ha hb hab
    have hval : f z=f u := by
      rw [← he,map_add,map_smul,map_smul,hfy]
      change a*f u+b*f u=f u
      rw [← add_mul,hab,one_mul]
    refine ⟨hzP,?_⟩
    intro w hw
    change f w ≤ f z
    rw [hval]
    exact (hs w hw).1
  · rintro ⟨hz,hmax⟩
    have hlo := hmax u huP
    change f u ≤ f z at hlo
    exact (hs z hz).2 (le_antisymm (hs z hz).1 hlo)

lemma line_eval (h e : Form) (v z : Point) (hz : 0 < h (z-v)) (s t : ℝ) :
    (s • e+t • h) z-(s • e+t • h) v =
      h (z-v)*(s*(e (z-v)/h (z-v))+t) := by
  have hn : h z-h v ≠ 0 := by simpa only [map_sub] using (ne_of_gt hz)
  change s*e z+t*h z-(s*e v+t*h v) = h (z-v)*(s*(e (z-v)/h (z-v))+t)
  simp only [map_sub]
  field_simp [hn]
  <;> ring

lemma line_slack (h e : Form) (v z : Point) (hz : 0 < h (z-v)) (s t : ℝ) :
    (s • e+t • h) v+1-(s • e+t • h) z =
      h (z-v)*(1/h (z-v)-(s*(e (z-v)/h (z-v))+t)) := by
  have hh := line_eval h e v z hz s t
  have hi : h (z-v)*(1/h (z-v))=1 := by
    rw [mul_comm]; exact div_mul_cancel₀ _ (ne_of_gt hz)
  nlinarith

/-- A complete lower secant lifts to an original exposed segment, not an edge
of an auxiliary graph. The target is strictly below this original support. -/
theorem secant_edge {n : ℕ} (v : Point) (p : Fin (n+1) → Point) (h e : Form)
    (hpos : ∀ i, 0 < h (p i-v))
    (hw : StrictMono (fun i => e (p i-v)/h (p i-v)))
    (ha : Hirsch.ConvexChainRank.StrictChain
      (fun i => e (p i-v)/h (p i-v)) (fun i => 1/h (p i-v))) (j : Fin n) :
    IsExposed ℝ
      (convexHull ℝ ((insert v (Finset.univ.image p) : Finset Point) : Set Point))
      (segment ℝ (p j.castSucc) (p j.succ)) := by
  classical
  let C := insert v (Finset.univ.image p)
  let w := fun i => e (p i-v)/h (p i-v)
  let a := fun i => 1/h (p i-v)
  obtain ⟨s,t,hu,hy,hall⟩ := consecutive_secant w a hw ha j
  let f : Form := s • e+t • h
  let M := f v+1
  have hs : ∀ i, M-f (p i)=h (p i-v)*(a i-(s*w i+t)) := by
    intro i
    exact line_slack h e v (p i) (hpos i) s t
  have hf0 : f (p j.castSucc)=M := by
    have hh := hs j.castSucc
    rw [hu,sub_self,mul_zero] at hh
    linarith
  have hf1 : f (p j.succ)=M := by
    have hh := hs j.succ
    rw [hy,sub_self,mul_zero] at hh
    linarith
  have hgen : ∀ i, f (p i) ≤ M ∧ (f (p i)=M → i=j.castSucc ∨ i=j.succ) := by
    intro i
    have hnon := mul_nonneg (hpos i).le (sub_nonneg.mpr (hall i).1)
    constructor
    · rw [← hs i] at hnon
      linarith
    · intro he
      have hz : h (p i-v)*(a i-(s*w i+t))=0 := by rw [← hs i,he,sub_self]
      have hdiff := (mul_eq_zero.mp hz).resolve_left (ne_of_gt (hpos i))
      exact (hall i).2 (sub_eq_zero.mp hdiff).symm
  apply exposed_segment C (p j.castSucc) (p j.succ)
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩))
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩))
    f (hf1.trans hf0.symm)
  intro z hz
  rcases Finset.mem_insert.mp hz with hz | hz
  · subst z
    refine ⟨?_,?_⟩
    · rw [hf0]; dsimp [M]; linarith
    · intro he
      rw [hf0] at he
      dsimp [M] at he
      linarith
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    refine ⟨by rw [hf0]; exact (hgen i).1,?_⟩
    intro he
    have hc := (hgen i).2 (he.trans hf0)
    exact hc.imp (congrArg p) (congrArg p)

/-- An extreme normalized ray exposes the whole original target edge. -/
lemma ray_edge {n : ℕ} (v : Point) (p : Fin (n+1) → Point) (h e : Form)
    (hpos : ∀ i, 0 < h (p i-v)) (j : Fin (n+1)) (s : ℝ)
    (hmax : ∀ i, s*(e (p i-v)/h (p i-v)) ≤ s*(e (p j-v)/h (p j-v)))
    (heq : ∀ i, s*(e (p i-v)/h (p i-v))=s*(e (p j-v)/h (p j-v)) → i=j) :
    IsExposed ℝ
      (convexHull ℝ ((insert v (Finset.univ.image p) : Finset Point) : Set Point))
      (segment ℝ v (p j)) := by
  classical
  let C := insert v (Finset.univ.image p)
  let w := fun i => e (p i-v)/h (p i-v)
  let f : Form := s • e+(-s*w j) • h
  have hs : ∀ i, f (p i)-f v=h (p i-v)*(s*w i-s*w j) := by
    intro i
    simpa only [f,w,sub_eq_add_neg,neg_mul] using line_eval h e v (p i) (hpos i) s (-s*w j)
  have hj : f (p j)=f v := by
    have hh := hs j
    rw [sub_self,mul_zero] at hh
    exact sub_eq_zero.mp hh
  apply exposed_segment C v (p j) (Finset.mem_insert_self _ _)
    (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)) f hj
  intro z hz
  rcases Finset.mem_insert.mp hz with hz | hz
  · subst z
    exact ⟨le_rfl,fun _ => Or.inl rfl⟩
  · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    have hnon := mul_nonpos_of_nonneg_of_nonpos (hpos i).le (sub_nonpos.mpr (hmax i))
    refine ⟨?_,?_⟩
    · rw [← hs i] at hnon
      exact sub_nonpos.mp hnon
    · intro hval
      have hz : h (p i-v)*(s*w i-s*w j)=0 := by rw [← hs i,hval,sub_self]
      have hc := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (ne_of_gt (hpos i)))
      exact Or.inr (congrArg p (heq i hc))

end Hirsch.RadialPolygon
namespace Hirsch.RadialPolygon

open Set

/-- Internal original-edge walk; the public result exports a finite sequence. -/
structure Walk (P : Set Point) (u v : Point) where
  length : ℕ
  point : ℕ → Point
  first : point 0=u
  last : point length=v
  vertex : ∀ i, i ≤ length → point i ∈ P.extremePoints ℝ
  step : ∀ i, i < length → point i ≠ point (i+1) ∧
    IsExposed ℝ P (segment ℝ (point i) (point (i+1)))

namespace Walk

def nil {P : Set Point} {u : Point} (hu : u ∈ P.extremePoints ℝ) : Walk P u u where
  length := 0
  point := fun _ => u
  first := rfl
  last := rfl
  vertex := fun _ _ => hu
  step := by intro i hi; omega

def prepend {P : Set Point} {u v w : Point} (hu : u ∈ P.extremePoints ℝ)
    (he : u ≠ v ∧ IsExposed ℝ P (segment ℝ u v)) (q : Walk P v w) : Walk P u w where
  length := q.length+1
  point := fun i => if i=0 then u else q.point (i-1)
  first := by simp
  last := by simpa using q.last
  vertex := by
    intro i hi
    by_cases hz : i=0
    · simpa [hz] using hu
    · simpa [hz] using q.vertex (i-1) (by omega)
  step := by
    intro i hi
    cases i with
    | zero => simpa [q.first] using he
    | succ i => simpa using q.step i (by omega)

end Walk

/-- Construct both boundary walks and select the shorter one. No route or
adjacency oracle is supplied beyond the original segments derived below. -/
lemma chain_walks {n : ℕ} (P : Set Point) (v : Point) (p : Fin (n+1) → Point)
    (hv : v ∈ P.extremePoints ℝ) (hp : ∀ i, p i ∈ P.extremePoints ℝ)
    (hfirst : p 0 ≠ v ∧ IsExposed ℝ P (segment ℝ (p 0) v))
    (hlast : p (Fin.last n) ≠ v ∧ IsExposed ℝ P (segment ℝ (p (Fin.last n)) v))
    (hedge : ∀ j : Fin n, p j.castSucc ≠ p j.succ ∧
      IsExposed ℝ P (segment ℝ (p j.castSucc) (p j.succ))) (k : Fin (n+1)) :
    ∃ q : Walk P (p k) v, q.length=min k.val (n-k.val)+1 := by
  have left : ∀ j : ℕ, (hj : j ≤ n) →
      ∃ q : Walk P (p ⟨j,by omega⟩) v, q.length=j+1 := by
    intro j
    induction j with
    | zero =>
      intro hj
      exact ⟨Walk.prepend (hp 0) hfirst (Walk.nil hv),rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨q,hq⟩ := ih (by omega)
      let a : Fin n := ⟨j,by omega⟩
      have he := hedge a
      have her : p a.succ ≠ p a.castSucc ∧
          IsExposed ℝ P (segment ℝ (p a.succ) (p a.castSucc)) :=
        ⟨he.1.symm,by simpa only [segment_symm] using he.2⟩
      refine ⟨Walk.prepend (hp a.succ) her q,?_⟩
      change q.length+1=j+1+1
      omega
  have right : ∀ r : ℕ, ∀ j : Fin (n+1), n-j.val=r →
      ∃ q : Walk P (p j) v, q.length=r+1 := by
    intro r
    induction r with
    | zero =>
      intro j hj
      have he : j=Fin.last n := by apply Fin.ext; have ht := j.isLt; change j.val=n; omega
      subst j
      exact ⟨Walk.prepend (hp (Fin.last n)) hlast (Walk.nil hv),rfl⟩
    | succ r ih =>
      intro j hj
      have hjn : j.val < n := by omega
      let a : Fin n := ⟨j.val,hjn⟩
      obtain ⟨q,hq⟩ := ih a.succ (by change n-(j.val+1)=r; omega)
      refine ⟨Walk.prepend (hp j) (hedge a) q,?_⟩
      change q.length+1=r+1+1
      omega
  by_cases hk : k.val ≤ n-k.val
  · obtain ⟨q,hq⟩ := left k.val (by have hh := k.isLt; omega)
    exact ⟨q,by rw [min_eq_left hk]; exact hq⟩
  · obtain ⟨q,hq⟩ := right (n-k.val) k rfl
    exact ⟨q,by rw [min_eq_right (by omega : n-k.val ≤ k.val)]; exact hq⟩

/-- Derive the original exposed segments and construct the complete walk from
an actual planar-vertex chart; strict chart convexity is not a premise. -/
theorem original_routes {n : ℕ} (P : Set Point) (v : Point) (p : Fin (n+1) → Point)
    (h e : Form)
    (hP : P=convexHull ℝ ((insert v (Finset.univ.image p) : Finset Point) : Set Point))
    (hv : v ∈ P.extremePoints ℝ) (hp : ∀ i, p i ∈ P.extremePoints ℝ)
    (hpos : ∀ i, 0 < h (p i-v))
    (hinj : Function.Injective (fun z : Point => (h z,e z)))
    (hw : StrictMono (fun i => e (p i-v)/h (p i-v))) :
    Hirsch.ConvexChainRank.StrictChain
      (fun i => e (p i-v)/h (p i-v)) (fun i => 1/h (p i-v)) ∧
    (p 0 ≠ v ∧ IsExposed ℝ P (segment ℝ (p 0) v)) ∧
    (p (Fin.last n) ≠ v ∧ IsExposed ℝ P (segment ℝ (p (Fin.last n)) v)) ∧
    (∀ j : Fin n, p j.castSucc ≠ p j.succ ∧
      IsExposed ℝ P (segment ℝ (p j.castSucc) (p j.succ))) ∧
    ∀ k : Fin (n+1), ∃ q : Walk P (p k) v, q.length=min k.val (n-k.val)+1 := by
  classical
  let w := fun i => e (p i-v)/h (p i-v)
  have hcv : Convex ℝ P := by rw [hP]; exact convex_convexHull ℝ _
  have hc := vertex_chain P hcv v p h e hv.1 hp hpos hinj hw
  have hne : ∀ i, p i ≠ v := by
    intro i he
    have hi := hpos i
    rw [he,sub_self,map_zero] at hi
    exact (lt_irrefl _) hi
  have hp_inj : Function.Injective p := by
    intro i j he
    apply hw.injective
    simp only [he]
  have hlo : IsExposed ℝ P (segment ℝ (p 0) v) := by
    rw [hP]
    have hh := ray_edge v p h e hpos 0 (-1)
      (fun i => by have hi := hw.monotone (show (0 : Fin (n+1)) ≤ i from by change (0 : ℕ) ≤ i.val; exact Nat.zero_le _); linarith)
      (fun i he => hw.injective (by linarith))
    simpa only [segment_symm] using hh
  have hhi : IsExposed ℝ P (segment ℝ (p (Fin.last n)) v) := by
    rw [hP]
    have hh := ray_edge v p h e hpos (Fin.last n) 1
      (fun i => by simpa only [one_mul] using hw.monotone (show i ≤ Fin.last n from by have ht := i.isLt; change i.val ≤ n; omega))
      (fun i he => hw.injective (by simpa only [one_mul] using he))
    simpa only [segment_symm] using hh
  have hed : ∀ j : Fin n, p j.castSucc ≠ p j.succ ∧
      IsExposed ℝ P (segment ℝ (p j.castSucc) (p j.succ)) := by
    intro j
    refine ⟨?_,?_⟩
    · intro he
      have hi := congrArg Fin.val (hp_inj he)
      change j.val=j.val+1 at hi
      omega
    · rw [hP]
      exact secant_edge v p h e hpos hw hc j
  exact ⟨hc,⟨hne 0,hlo⟩,⟨hne (Fin.last n),hhi⟩,hed,
    chain_walks P v p hv hp ⟨hne 0,hlo⟩ ⟨hne (Fin.last n),hhi⟩ hed⟩

end Hirsch.RadialPolygon
/-- Actual planar vertices force a strict radial chain and support original exposed-
edge walks attaining its exact inverse-height rank. -/
theorem solution (n : ℕ) (P : Set (Fin 2 → ℝ)) (v : Fin 2 → ℝ)
    (p : Fin (n+1) → (Fin 2 → ℝ))
    (h e : (Fin 2 → ℝ) →ₗ[ℝ] ℝ)
    (hP : P=convexHull ℝ ((insert v (Finset.univ.image p) : Finset (Fin 2 → ℝ)) : Set (Fin 2 → ℝ)))
    (hv : v ∈ P.extremePoints ℝ) (hp : ∀ i, p i ∈ P.extremePoints ℝ)
    (hpos : ∀ i, 0 < h (p i-v))
    (hinj : Function.Injective (fun z : Fin 2 → ℝ => (h z,e z)))
    (hw : StrictMono (fun i => e (p i-v)/h (p i-v))) :
    let w := fun i => e (p i-v)/h (p i-v)
    let a := fun i => 1/h (p i-v)
    let U := fun (t : ℝ) (k : Fin (n+1)) =>
      @Finset.filter ℝ (fun z => a k+t*w k < z) (fun _ => Classical.propDecidable _)
        (Finset.univ.image (fun i => a i+t*w i))
    let B := fun (t c : ℝ) (k : Fin (n+1)) =>
      @Finset.filter ℝ (fun z => z < 1/(a k+t*w k+c)) (fun _ => Classical.propDecidable _)
        (insert 0 (Finset.univ.image (fun i => 1/(a i+t*w i+c))))
    (∀ i j k : Fin (n+1), i < j → j < k →
      (a j-a i)*(w k-w j) < (a k-a j)*(w j-w i)) ∧
    (p 0 ≠ v ∧ IsExposed ℝ P (segment ℝ (p 0) v)) ∧
    (p (Fin.last n) ≠ v ∧ IsExposed ℝ P (segment ℝ (p (Fin.last n)) v)) ∧
    (∀ j : Fin n, p j.castSucc ≠ p j.succ ∧
      IsExposed ℝ P (segment ℝ (p j.castSucc) (p j.succ))) ∧
    ∃ M : ℝ, 0 < M ∧ ∀ k : Fin (n+1),
      (∀ t : ℝ, min k.val (n-k.val) ≤ (U t k).card) ∧
      (U (-M) k).card=k.val ∧ (U M k).card=n-k.val ∧
      ∃ L : ℕ, L=min k.val (n-k.val)+1 ∧ 2*L ≤ n+2 ∧
        (∀ t : ℝ, L ≤ (U t k).card+1) ∧
        (∃ t c : ℝ, (t=M ∨ t=-M) ∧ (∀ i, 0 < a i+t*w i+c) ∧ (B t c k).card=L) ∧
        ∃ q : Fin (L+1) → (Fin 2 → ℝ), q 0=p k ∧ q (Fin.last L)=v ∧
          (∀ i, q i ∈ P.extremePoints ℝ) ∧
          ∀ i : Fin L, q i.castSucc ≠ q i.succ ∧
            IsExposed ℝ P (segment ℝ (q i.castSucc) (q i.succ)) := by
  classical
  let w := fun i => e (p i-v)/h (p i-v)
  let a := fun i => 1/h (p i-v)
  let U := fun (t : ℝ) (k : Fin (n+1)) =>
    @Finset.filter ℝ (fun z => a k+t*w k < z) (fun _ => Classical.propDecidable _)
      (Finset.univ.image (fun i => a i+t*w i))
  let B := fun (t c : ℝ) (k : Fin (n+1)) =>
    @Finset.filter ℝ (fun z => z < 1/(a k+t*w k+c)) (fun _ => Classical.propDecidable _)
      (insert 0 (Finset.univ.image (fun i => 1/(a i+t*w i+c))))
  have hU : ∀ t k, Hirsch.ConvexChainRank.above (fun i => a i+t*w i) k=U t k := by
    intro t k
    ext z
    simp only [Hirsch.ConvexChainRank.above,U,Finset.mem_filter,Finset.mem_image]
  have hB : ∀ t c k, Hirsch.ConvexChainRank.below (fun i => a i+t*w i+c) k=B t c k := by
    intro t c k
    ext z
    simp only [Hirsch.ConvexChainRank.below,B,Finset.mem_filter,Finset.mem_insert,Finset.mem_image]
  obtain ⟨hc,hfirst,hlast,hedge,hroutes⟩ := Hirsch.RadialPolygon.original_routes
    P v p h e hP hv hp hpos hinj hw
  obtain ⟨M,hM,hall⟩ := Hirsch.ConvexChainRank.exact_rank w a hw hc
  refine ⟨hc,hfirst,hlast,hedge,M,hM,?_⟩
  intro k
  obtain ⟨hlo,hl,hr,t,c,ht,hcpos,hac,hbc,hbound⟩ := hall k
  obtain ⟨q,hq⟩ := hroutes k
  have hbc' : (B t c k).card=q.length := by
    rw [hq]
    simpa only [hB] using hbc
  refine ⟨?_,?_,?_,q.length,hq,?_,?_,⟨t,c,ht,hcpos,hbc'⟩,
    (fun i => q.point i.val),q.first,q.last,?_,?_⟩
  · simpa only [hU] using hlo
  · simpa only [hU] using hl
  · simpa only [hU] using hr
  · have hb' : 2*(B t c k).card ≤ n+2 := by simpa only [hB] using hbound
    simpa only [hbc'] using hb'
  · intro t
    rw [hq]
    have hh := Nat.add_le_add_right (hlo t) 1
    simpa only [hU] using hh
  · intro i
    exact q.vertex i.val (by have hi := i.isLt; omega)
  · intro i
    exact q.step i.val i.isLt

#print axioms Hirsch.ConvexChainRank.exact_rank
#print axioms Hirsch.RadialPolygon.radial_mass_gt_one
#print axioms Hirsch.RadialPolygon.vertex_chain
#print axioms Hirsch.RadialPolygon.secant_edge
#print axioms Hirsch.RadialPolygon.ray_edge
#print axioms Hirsch.RadialPolygon.original_routes
#print axioms solution
