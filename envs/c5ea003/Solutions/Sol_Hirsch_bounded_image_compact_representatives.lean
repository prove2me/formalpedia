-- Prove2me | solution 1 for Hirsch.bounded_image_compact_representatives
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-14T21:18:44.835809+00:00
-- url     : https://prove2.me/submissions/0a3332a7-8c22-4fe4-90c1-9fd858b95a71

import Mathlib

open Set
open scoped BigOperators

namespace Hirsch.BoundedRepresentatives

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def supp (x : ι → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => x i ≠ 0)

@[simp] lemma mem_supp (x : ι → ℝ) (i : ι) : i ∈ supp x ↔ x i ≠ 0 := by
  classical
  simp [supp]

/-- No nonzero nonnegative kernel vector is supported in this coordinate face. -/
def NullFree (A : (ι → ℝ) →L[ℝ] E) (s : Finset ι) : Prop :=
  ∀ z : ι → ℝ, (∀ i, 0 ≤ z i) → (∀ i, i ∉ s → z i = 0) → A z = 0 → z = 0

private lemma positive_coordinate (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hne : x ≠ 0) : ∃ i, 0 < x i := by
  by_contra h
  push_neg at h
  apply hne
  funext i
  exact le_antisymm (h i) (hx i)

private lemma mass_pos (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) (hne : x ≠ 0) :
    0 < ∑ i, x i := by
  obtain ⟨j, hj⟩ := positive_coordinate x hx hne
  exact hj.trans_le (Finset.single_le_sum (fun i _ => hx i) (Finset.mem_univ j))

/-- Exact minimum-ratio removal of a supported nonnegative null direction. -/
private lemma prune (x z : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hz : ∀ i, 0 ≤ z i) (hz0 : z ≠ 0) (hsub : supp z ⊆ supp x) :
    ∃ t : ℝ, 0 < t ∧ (∀ i, 0 ≤ (x - t • z) i) ∧
      supp (x - t • z) ⊂ supp x := by
  classical
  let s : Finset ι := Finset.univ.filter (fun i => 0 < z i)
  have hs : s.Nonempty := by
    obtain ⟨i, hi⟩ := positive_coordinate z hz hz0
    exact ⟨i, by simp [s, hi]⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image s (fun j => x j / z j) hs
  have hzi : 0 < z i := (Finset.mem_filter.mp hi).2
  have hxi : 0 < x i := by
    have hne := (mem_supp x i).mp (hsub ((mem_supp z i).mpr (ne_of_gt hzi)))
    exact lt_of_le_of_ne (hx i) (Ne.symm hne)
  let t : ℝ := x i / z i
  have ht : 0 < t := div_pos hxi hzi
  have hti : t * z i = x i := div_mul_cancel₀ _ (ne_of_gt hzi)
  have hnon : ∀ j, 0 ≤ (x - t • z) j := by
    intro j
    change 0 ≤ x j - t * z j
    by_cases hj : 0 < z j
    · have hr : t ≤ x j / z j := hmin j (by simp [s, hj])
      have hp := (le_div_iff₀ hj).mp hr
      linarith
    · have hj0 : z j = 0 := le_antisymm (le_of_not_gt hj) (hz j)
      simpa [hj0] using hx j
  have hout : ∀ j, x j = 0 → z j = 0 := by
    intro j hxj
    by_contra hzj
    exact ((mem_supp x j).mp (hsub ((mem_supp z j).mpr hzj))) hxj
  have hsmall : supp (x - t • z) ⊆ supp x := by
    intro j hj
    apply (mem_supp x j).mpr
    intro hxj
    have hneq := (mem_supp (x - t • z) j).mp hj
    apply hneq
    change x j - t * z j = 0
    simp [hxj, hout j hxj]
  have hiout : i ∉ supp (x - t • z) := by
    intro hi'
    have hneq := (mem_supp (x - t • z) i).mp hi'
    apply hneq
    change x i - t * z i = 0
    linarith
  refine ⟨t, ht, hnon, Finset.ssubset_iff_subset_ne.mpr ⟨hsmall, ?_⟩⟩
  intro heq
  apply hiout
  rw [heq]
  exact (mem_supp x i).mpr (ne_of_gt hxi)

/-- Removing positive null directions terminates by STRICT support descent.
It retains the exact image and never introduces a new nonzero coordinate. -/
theorem exists_nullFree_representative (A : (ι → ℝ) →L[ℝ] E)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ A y = A x ∧
      supp y ⊆ supp x ∧ NullFree A (supp y) := by
  classical
  have go : ∀ m : ℕ, ∀ u : ι → ℝ, (∀ i, 0 ≤ u i) → (supp u).card = m →
      ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ A y = A u ∧
        supp y ⊆ supp u ∧ NullFree A (supp y) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro u hu hcard
      by_cases hg : NullFree A (supp u)
      · exact ⟨u, hu, rfl, (fun _ hi => hi), hg⟩
      · simp only [NullFree] at hg
        push_neg at hg
        obtain ⟨z, hz, hzout, hAz, hz0⟩ := hg
        have hsub : supp z ⊆ supp u := by
          intro i hi
          by_contra hout
          exact ((mem_supp z i).mp hi) (hzout i hout)
        obtain ⟨t, ht, hv, hs⟩ := prune u z hu hz hz0 hsub
        have hlt : (supp (u - t • z)).card < m := by
          rw [← hcard]
          exact Finset.card_lt_card hs
        obtain ⟨y, hy, hAy, hysub, hgood⟩ :=
          ih _ hlt (u - t • z) hv rfl
        refine ⟨y, hy, ?_, hysub.trans (Finset.ssubset_iff_subset_ne.mp hs).1, hgood⟩
        calc
          A y = A (u - t • z) := hAy
          _ = A u := by simp [map_sub, map_smul, hAz]
  exact go (supp x).card x hx rfl

/-- Compact normalized nonnegative vectors on a fixed support. -/
def sectionSet (s : Finset ι) : Set (ι → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1 ∧ ∀ i, i ∉ s → x i = 0}

lemma sectionSet_compact (s : Finset ι) : IsCompact (sectionSet s) := by
  classical
  have he : sectionSet s =
      (Set.Icc (0 : ι → ℝ) (fun _ => 1) ∩ {x | (∑ i, x i) = 1}) ∩
        {x : ι → ℝ | ∀ i, i ∉ s → x i = 0} := by
    ext x
    constructor
    · rintro ⟨hx, hm, ho⟩
      refine ⟨⟨⟨hx, ?_⟩, hm⟩, ho⟩
      intro i
      have h := Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)
      simpa only [hm] using h
    · rintro ⟨⟨⟨hx, _⟩, hm⟩, ho⟩
      exact ⟨hx, hm, ho⟩
  have hmass : IsClosed {x : ι → ℝ | (∑ i, x i) = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  have hout : IsClosed {x : ι → ℝ | ∀ i, i ∉ s → x i = 0} := by
    simp only [setOf_forall]
    exact isClosed_iInter (fun i => isClosed_iInter
      (fun _ => isClosed_eq (continuous_apply i) continuous_const))
  rw [he]
  exact (isCompact_Icc.inter_right hmass).inter_right hout

private lemma normalized_mem (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hx0 : x ≠ 0) (s : Finset ι) (hout : ∀ i, i ∉ s → x i = 0) :
    ((∑ i, x i)⁻¹ • x) ∈ sectionSet s := by
  have hm := mass_pos x hx hx0
  refine ⟨fun i => mul_nonneg (inv_pos.mpr hm).le (hx i), ?_, ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    exact inv_mul_cancel₀ (ne_of_gt hm)
  · intro i hi
    simp [Pi.smul_apply, hout i hi]

/-- On a null-free coordinate face, normalized image norms have a positive
minimum. Rescaling gives a homogeneous bound on every nonnegative preimage. -/
theorem bound_on_nullFree_support (A : (ι → ℝ) →L[ℝ] E)
    (s : Finset ι) (hs : NullFree A s) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ι → ℝ,
      (∀ i, 0 ≤ x i) → (∀ i, i ∉ s → x i = 0) →
      (∑ i, x i) ≤ C * ‖A x‖ := by
  classical
  by_cases hne : (sectionSet s).Nonempty
  · obtain ⟨z, hz, hmin⟩ := (sectionSet_compact s).exists_isMinOn hne
      (A.continuous.norm.continuousOn)
    have haz : A z ≠ 0 := by
      intro he
      have hz0 := hs z hz.1 hz.2.2 he
      have hm := hz.2.1
      simp [hz0] at hm
    have hn : 0 < ‖A z‖ := norm_pos_iff.mpr haz
    refine ⟨‖A z‖⁻¹, inv_pos.mpr hn, ?_⟩
    intro x hx hout
    by_cases hx0 : x = 0
    · simp [hx0]
    · have hm := mass_pos x hx hx0
      let v : ι → ℝ := (∑ i, x i)⁻¹ • x
      have hv : v ∈ sectionSet s := normalized_mem x hx hx0 s hout
      have hsmall : ‖A z‖ ≤ ‖A v‖ := (isMinOn_iff.mp hmin) v hv
      have hscaled : (∑ i, x i) * ‖A v‖ = ‖A x‖ := by
        dsimp only [v]
        rw [map_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hm.le)]
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hm), one_mul]
      have hprod := mul_le_mul_of_nonneg_left hsmall hm.le
      rw [hscaled] at hprod
      have hdiv : (∑ i, x i) ≤ ‖A x‖ / ‖A z‖ := (le_div_iff₀ hn).mpr hprod
      simpa only [div_eq_mul_inv, mul_comm] using hdiv
  · refine ⟨1, by norm_num, ?_⟩
    intro x hx hout
    have hx0 : x = 0 := by
      by_contra hz
      exact hne ⟨_, normalized_mem x hx hz s hout⟩
    simp [hx0]

/-- A UNIFORM constant for all nonnegative image fibers. No injectivity,
pointedness of the image cone or boundedness of the full preimage is assumed. -/
theorem nonnegative_fiber_bound (A : (ι → ℝ) →L[ℝ] E) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ι → ℝ, (∀ i, 0 ≤ x i) →
      ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ A y = A x ∧
        supp y ⊆ supp x ∧ (∑ i, y i) ≤ C * ‖A x‖ := by
  classical
  have hlocal : ∀ s : Finset ι, ∃ c : ℝ, 0 < c ∧
      (NullFree A s → ∀ x : ι → ℝ, (∀ i, 0 ≤ x i) →
        (∀ i, i ∉ s → x i = 0) → (∑ i, x i) ≤ c * ‖A x‖) := by
    intro s
    by_cases hs : NullFree A s
    · obtain ⟨c, hc, hb⟩ := bound_on_nullFree_support A s hs
      exact ⟨c, hc, fun _ => hb⟩
    · exact ⟨1, by norm_num, fun h => False.elim (hs h)⟩
  choose c hc hbound using hlocal
  let C : ℝ := 1 + ∑ s : Finset ι, c s
  have hsum : 0 ≤ ∑ s : Finset ι, c s := Finset.sum_nonneg (fun s _ => (hc s).le)
  have hC : 0 < C := by dsimp only [C]; linarith
  have hcC (s : Finset ι) : c s ≤ C := by
    have h := Finset.single_le_sum (fun t _ => (hc t).le) (Finset.mem_univ s)
    dsimp only [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro x hx
  obtain ⟨y, hy, hAy, hsub, hgood⟩ := exists_nullFree_representative A x hx
  have hout : ∀ i, i ∉ supp y → y i = 0 := by
    intro i hi
    by_contra hne
    exact hi ((mem_supp y i).mpr hne)
  have hb := hbound (supp y) hgood y hy hout
  refine ⟨y, hy, hAy, hsub, ?_⟩
  rw [hAy] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (hcC _) (norm_nonneg _))

/-- Slack augmentation preserves inequalities and the image exactly. The
constant depends ONLY on B and G, not on t, the chosen point, or an image bound. -/
theorem allocation_representative_bound {k r d : ℕ}
    (B : (Fin k → ℝ) →L[ℝ] (Fin r → ℝ))
    (G : (Fin k → ℝ) →L[ℝ] (Fin d → ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : Fin r → ℝ) (x : Fin k → ℝ),
      (∀ i, 0 ≤ x i) → (∀ q, B x q ≤ t q) →
      ∃ y : Fin k → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ q, B y q ≤ t q) ∧
        G y = G x ∧ (∀ i, x i = 0 → y i = 0) ∧
        (∀ q, B x q = t q → B y q = t q) ∧
        (∑ i, y i) ≤ C * (‖t‖ + ‖G x‖) := by
  classical
  let A : (Sum (Fin k) (Fin r) → ℝ) →L[ℝ] ((Fin r → ℝ) × (Fin d → ℝ)) :=
    { toFun := fun z =>
        (B (fun i => z (Sum.inl i)) + (fun q => z (Sum.inr q)),
          G (fun i => z (Sum.inl i)))
      map_add' := by
        intro u v
        apply Prod.ext
        · change B ((fun i => u (Sum.inl i)) + (fun i => v (Sum.inl i))) +
            ((fun q => u (Sum.inr q)) + (fun q => v (Sum.inr q))) =
            (B (fun i => u (Sum.inl i)) + (fun q => u (Sum.inr q))) +
              (B (fun i => v (Sum.inl i)) + (fun q => v (Sum.inr q)))
          rw [map_add]
          abel
        · exact G.map_add _ _
      map_smul' := by
        intro c z
        apply Prod.ext
        · change B (c • (fun i => z (Sum.inl i))) + c • (fun q => z (Sum.inr q)) =
            c • (B (fun i => z (Sum.inl i)) + (fun q => z (Sum.inr q)))
          rw [map_smul, smul_add]
        · exact G.map_smul c _
      cont := by fun_prop }
  obtain ⟨C, hC, hbound⟩ := nonnegative_fiber_bound A
  refine ⟨C, hC, ?_⟩
  intro t x hx hBx
  let u : Sum (Fin k) (Fin r) → ℝ := Sum.elim x (t - B x)
  have hu : ∀ i, 0 ≤ u i := by
    intro i
    cases i with
    | inl i => exact hx i
    | inr q => exact sub_nonneg.mpr (hBx q)
  have hAu : A u = (t, G x) := by
    apply Prod.ext
    · change B x + (t - B x) = t
      abel
    · rfl
  obtain ⟨v, hv, hAv, hsub, hmass⟩ := hbound u hu
  let y : Fin k → ℝ := fun i => v (Sum.inl i)
  have hy : ∀ i, 0 ≤ y i := fun i => hv (Sum.inl i)
  have hBy : ∀ q, B y q ≤ t q := by
    intro q
    have he := congrArg (fun p : (Fin r → ℝ) × (Fin d → ℝ) => p.1 q) (hAv.trans hAu)
    change B y q + v (Sum.inr q) = t q at he
    linarith [hv (Sum.inr q)]
  have hGy : G y = G x := congrArg Prod.snd (hAv.trans hAu)
  have hzero : ∀ i, x i = 0 → y i = 0 := by
    intro i hxi
    by_contra hne
    have hi := (mem_supp u (Sum.inl i)).mp
      (hsub ((mem_supp v (Sum.inl i)).mpr hne))
    exact hi hxi
  have htight : ∀ q, B x q = t q → B y q = t q := by
    intro q hq
    have hu0 : u (Sum.inr q) = 0 := by
      change t q - B x q = 0
      rw [hq, sub_self]
    have hv0 : v (Sum.inr q) = 0 := by
      by_contra hne
      exact ((mem_supp u (Sum.inr q)).mp
        (hsub ((mem_supp v (Sum.inr q)).mpr hne))) hu0
    have he := congrArg (fun p : (Fin r → ℝ) × (Fin d → ℝ) => p.1 q) (hAv.trans hAu)
    change B y q + v (Sum.inr q) = t q at he
    simpa only [hv0, add_zero] using he
  have hysum : (∑ i, y i) ≤ ∑ i, v i := by
    rw [Fintype.sum_sum_type]
    have hnon : 0 ≤ ∑ q : Fin r, v (Sum.inr q) :=
      Finset.sum_nonneg (fun q _ => hv (Sum.inr q))
    change (∑ i : Fin k, v (Sum.inl i)) ≤ _
    linarith
  have hnorm : ‖A u‖ ≤ ‖t‖ + ‖G x‖ := by
    rw [hAu, Prod.norm_def]
    exact max_le (by linarith [norm_nonneg (G x)]) (by linarith [norm_nonneg t])
  exact ⟨y, hy, hBy, hGy, hzero, htight, hysum.trans (hmass.trans
    (mul_le_mul_of_nonneg_left hnorm hC.le))⟩

lemma capped_resource_compact {k r : ℕ}
    (B : (Fin k → ℝ) →L[ℝ] (Fin r → ℝ)) (t : Fin r → ℝ) (R : ℝ) :
    IsCompact {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧
      (∀ q, B x q ≤ t q) ∧ (∑ i, x i) ≤ R} := by
  have he : {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧
      (∀ q, B x q ≤ t q) ∧ (∑ i, x i) ≤ R} =
      (Set.Icc (0 : Fin k → ℝ) (fun _ => R) ∩ {x | (∑ i, x i) ≤ R}) ∩
        {x | ∀ q, B x q ≤ t q} := by
    ext x
    constructor
    · rintro ⟨hx, hB, hm⟩
      refine ⟨⟨⟨hx, ?_⟩, hm⟩, hB⟩
      intro i
      exact (Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)).trans hm
    · rintro ⟨⟨⟨hx, _⟩, hm⟩, hB⟩
      exact ⟨hx, hB, hm⟩
  have hm : IsClosed {x : Fin k → ℝ | (∑ i, x i) ≤ R} :=
    isClosed_le (by fun_prop) continuous_const
  have hb : IsClosed {x : Fin k → ℝ | ∀ q, B x q ≤ t q} := by
    simp only [setOf_forall]
    exact isClosed_iInter (fun q => isClosed_le (by fun_prop) continuous_const)
  rw [he]
  exact (isCompact_Icc.inter_right hm).inter_right hb

/-- Every bounded allocation IMAGE has exactly the same image after ONE finite
mass cap, even when the original coefficient polyhedron is unbounded. -/
theorem bounded_image_compact_representatives {k r d : ℕ}
    (B : (Fin k → ℝ) →L[ℝ] (Fin r → ℝ))
    (G : (Fin k → ℝ) →L[ℝ] (Fin d → ℝ))
    (t : Fin r → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (himage : ∀ x : Fin k → ℝ, (∀ i, 0 ≤ x i) →
      (∀ q, B x q ≤ t q) → ‖G x‖ ≤ M) :
    ∃ R : ℝ, 0 ≤ R ∧
      IsCompact {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧
        (∀ q, B x q ≤ t q) ∧ (∑ i, x i) ≤ R} ∧
      G '' {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∀ q, B x q ≤ t q} =
      G '' {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧
        (∀ q, B x q ≤ t q) ∧ (∑ i, x i) ≤ R} := by
  obtain ⟨C, hC, hc⟩ := allocation_representative_bound B G
  let R : ℝ := C * (‖t‖ + M)
  refine ⟨R, mul_nonneg hC.le (add_nonneg (norm_nonneg _) hM),
    capped_resource_compact B t R, ?_⟩
  apply Set.Subset.antisymm
  · rintro u ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hBy, hGy, _hzero, _htight, hm⟩ := hc t x hx.1 hx.2
    have hmR : (∑ i, y i) ≤ R := hm.trans
      (mul_le_mul_of_nonneg_left (add_le_add (le_refl ‖t‖) (himage x hx.1 hx.2)) hC.le)
    exact ⟨y, ⟨hy, hBy, hmR⟩, hGy⟩
  · rintro u ⟨x, hx, rfl⟩
    exact ⟨x, ⟨hx.1, hx.2.1⟩, rfl⟩

end Hirsch.BoundedRepresentatives

/-- Uniform nonnegative representatives and an exact compact replacement of
any bounded linear image. This does NOT bound the constant by dimensions. -/
theorem solution {k r d : ℕ}
    (B : (Fin k → ℝ) →L[ℝ] (Fin r → ℝ))
    (G : (Fin k → ℝ) →L[ℝ] (Fin d → ℝ)) :
    (∃ C : ℝ, 0 < C ∧ ∀ (t : Fin r → ℝ) (x : Fin k → ℝ),
      (∀ i, 0 ≤ x i) → (∀ q, B x q ≤ t q) →
      ∃ y : Fin k → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ q, B y q ≤ t q) ∧
        G y = G x ∧ (∀ i, x i = 0 → y i = 0) ∧
        (∀ q, B x q = t q → B y q = t q) ∧
        (∑ i, y i) ≤ C * (‖t‖ + ‖G x‖)) ∧
    (∀ (t : Fin r → ℝ) (M : ℝ), 0 ≤ M →
      (∀ x : Fin k → ℝ, (∀ i, 0 ≤ x i) →
        (∀ q, B x q ≤ t q) → ‖G x‖ ≤ M) →
      ∃ R : ℝ, 0 ≤ R ∧
        IsCompact {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧
          (∀ q, B x q ≤ t q) ∧ (∑ i, x i) ≤ R} ∧
        G '' {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∀ q, B x q ≤ t q} =
        G '' {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧
          (∀ q, B x q ≤ t q) ∧ (∑ i, x i) ≤ R}) := by
  exact ⟨Hirsch.BoundedRepresentatives.allocation_representative_bound B G,
    fun t M hM hi => Hirsch.BoundedRepresentatives.bounded_image_compact_representatives B G t M hM hi⟩

#print axioms Hirsch.BoundedRepresentatives.exists_nullFree_representative
#print axioms Hirsch.BoundedRepresentatives.nonnegative_fiber_bound
#print axioms Hirsch.BoundedRepresentatives.allocation_representative_bound
#print axioms Hirsch.BoundedRepresentatives.bounded_image_compact_representatives
#print axioms solution
