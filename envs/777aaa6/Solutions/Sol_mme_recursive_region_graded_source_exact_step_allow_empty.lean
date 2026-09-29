-- Prove2me | solution 1 for mme_recursive_region_graded_source_exact_step_allow_empty
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T03:28:57.572127+00:00
-- url     : https://prove2.me/submissions/f37ac6df-7f63-43bc-8fe7-4d51b5fc9970

import Definitions.Def_mme_recursive_profiled_CW_data
import Theorems.Thm_mme_recursive_region_computed_hash_selection
import Mathlib.Data.Nat.Log
import Theorems.Thm_mme_prescribed_cell_pair_pattern_concentration
import Theorems.Thm_mme_prescribed_cell_histogram_nonempty
import Definitions.Def_mme_recursive_region_parent_profiles
import Theorems.Thm_mme_prescribed_cell_parent_profile_concentration
import Theorems.Thm_mme_recursive_region_parent_profile_concentration
import Definitions.Def_mme_recursive_yz_hash_filter

open BigOperators MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false

private theorem event_union {U J : Type*} [Fintype U] [Nonempty U] [Fintype J]
    (bad : J → U → Prop) (B : ℝ)
    (hb : ∀ j, (𝔼 f : U, if bad j f then (1 : ℝ) else 0) ≤ B) :
    (𝔼 f : U, if ∃ j, bad j f then (1 : ℝ) else 0) ≤ Fintype.card J * B := by
  classical
  calc
    _ ≤ 𝔼 f : U, (∑ j : J, if bad j f then (1 : ℝ) else 0) := by
      apply Finset.expect_le_expect
      intro f _
      by_cases h : ∃ j, bad j f
      · obtain ⟨j,hj⟩ := h
        have ht := Finset.single_le_sum (f := fun j : J ↦ if bad j f then (1 : ℝ) else 0)
          (fun k _ ↦ by dsimp; split_ifs <;> norm_num) (Finset.mem_univ j)
        rw [if_pos ⟨j,hj⟩]
        simpa only [if_pos hj] using ht
      · simp [h]
    _ = ∑ j : J, (𝔼 f : U, if bad j f then (1 : ℝ) else 0) := Finset.expect_sum_comm _ _ _
    _ ≤ ∑ _ : J, B := Finset.sum_le_sum (fun j _ ↦ hb j)
    _ = _ := by simp

private theorem mme_prescribed_cell_parent_profile_concentration_allow_empty {P C W R : Type*} [Fintype P] [Fintype C] [Fintype W] [Fintype R]
    (cell : P → C) (mu : C → W → ℕ)
    (hmass : ∀ c, ∑ w, mu c w = Fintype.card {p : P // cell p = c})
    (n : R → ℕ) (q : (r : R) → Fin (n r) × Fin 2 → P)
    (hq : ∀ r, Function.Injective (q r))
    (center : R → (Fin 2 → W) → ℝ)
    (hcenter : ∀ r w, center r w =
      (∑ t : Fin (n r), ∏ h : Fin 2, ((mu (cell (q r (t,h))) (w h) : ℝ) /
        Fintype.card {p : P // cell p = cell (q r (t,h))})) / n r)
    (m : ℕ) (hm : 0 < m) (hmn : ∀ r, n r ≠ 0 → m ≤ n r)
    (hsize : ∀ r t h, m ≤ Fintype.card {p : P // cell p = cell (q r (t,h))})
    (eps : ℝ) (heps : 0 < eps) :
    (𝔼 f : {f : P → W // Useful cell mu f},
      if ∃ r w, eps ≤ |(Fintype.card {t : Fin (n r) // ∀ h, f.val (q r (t,h)) = w h} : ℝ) /
          n r - center r w| then (1 : ℝ) else 0) ≤
      25 * Fintype.card R * (Fintype.card W : ℝ) ^ 2 / ((m : ℝ) * eps ^ 2) := by
  classical
  let U := {f : P → W // Useful cell mu f}
  have hU := mme_prescribed_cell_histogram_nonempty cell mu hmass
  letI : Nonempty U := hU
  let bad (j : R × (Fin 2 → W)) (f : U) :=
    eps ≤ |(Fintype.card {t : Fin (n j.1) // ∀ h, f.val (q j.1 (t,h)) = j.2 h} : ℝ) /
      n j.1 - center j.1 j.2|
  have hb (j : R × (Fin 2 → W)) : (𝔼 f : U, if bad j f then (1 : ℝ) else 0) ≤
      25 / ((m : ℝ) * eps ^ 2) := by
    by_cases hz : n j.1 = 0
    · have hc : center j.1 j.2 = 0 := by simp [hcenter, hz]
      have hbad (f : U) : ¬ bad j f := by
        simp only [bad, hz, Nat.cast_zero, div_zero, hc, sub_zero, abs_zero]
        exact not_le_of_gt heps
      simp only [if_neg (hbad _)]
      simpa using (show (0 : ℝ) ≤ 25 / ((m : ℝ) * eps ^ 2) by positivity)
    have h := mme_prescribed_cell_pair_pattern_concentration cell mu (q j.1) (hq j.1) j.2 hU
      m hm (by simpa using hmn j.1 hz) (hsize j.1) eps heps
    have heq (f : {f : P → W // Useful cell mu f}) : ((∑ t : Fin (n j.1), if (∀ h : Fin 2, f.val (q j.1 (t,h)) = j.2 h) then (1 : ℝ) else 0) -
        ∑ t : Fin (n j.1), ∏ h : Fin 2, ((mu (cell (q j.1 (t,h))) (j.2 h) : ℝ) /
          Fintype.card {p : P // cell p = cell (q j.1 (t,h))})) / Fintype.card (Fin (n j.1)) =
        (Fintype.card {t : Fin (n j.1) // ∀ h, f.val (q j.1 (t,h)) = j.2 h} : ℝ) /
          n j.1 - center j.1 j.2 := by
      rw [hcenter, Fintype.card_fin, sub_div]
      congr 2
      simp only [Fintype.card_subtype, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    simpa only [heq, bad] using h
  have h := event_union bad (25 / ((m : ℝ) * eps ^ 2)) hb
  have hex (f : U) : (∃ j, bad j f) ↔
      ∃ r w, eps ≤ |(Fintype.card {t : Fin (n r) // ∀ h, f.val (q r (t,h)) = w h} : ℝ) /
          n r - center r w| := by simp only [bad, Prod.exists]
  simp only [hex, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Nat.cast_mul, Nat.cast_pow] at h
  convert h using 1; ring



open BigOperators MME MME.RecursiveYZ MME.RegionRealization
open scoped Classical
set_option autoImplicit false


private theorem full_cell_fiber {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (a : Address half R parent n) (r : Fin R)
    (c : MME.RecursiveThinSplit.Split half (parent r)) :
    Fintype.card {p : Position n // fullCell htotal a p = ⟨r,c⟩} =
      MME.RecursiveThinSplit.count (a r) c +
      MME.RecursiveThinSplit.count (a r) (complement (htotal r) c) := by
  classical
  let e : {p : Position n // fullCell htotal a p = ⟨r,c⟩} ≃
      {p : Fin (n r) × Fin 2 //
        (if p.2 = 0 then a r p.1 else complement (htotal r) (a r p.1)) = c} := {
    toFun := by
      rintro ⟨⟨r',t,h⟩,hp⟩
      have hr : r' = r := congrArg Sigma.fst hp
      subst r'
      exact ⟨(t,h), eq_of_heq (Sigma.mk.inj hp).2⟩
    invFun := fun p ↦ ⟨⟨r,p.val⟩, by
      change (⟨r,_⟩ : Cell half R parent) = ⟨r,c⟩
      rw [p.property]⟩
    left_inv := by
      rintro ⟨⟨r',t,h⟩,hp⟩
      have hr : r' = r := congrArg Sigma.fst hp
      subst r'
      rfl
    right_inv := by intro p; rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  have hc (t : Fin (n r)) : complement (htotal r) (a r t) = c ↔
      a r t = complement (htotal r) c := by
    constructor
    · intro h
      simpa only [complement_complement] using congrArg (complement (htotal r)) h
    · intro h
      rw [h, complement_complement]
  simp only [show (1 : Fin 2) ≠ 0 by decide, 
    MME.RecursiveThinSplit.count, Finset.card_eq_sum_ones, Finset.sum_filter,
    Finset.sum_add_distrib]
  simp only [ite_true, ite_false, hc]
  congr 1

private theorem weighted_histogram {T C : Type*} [Fintype T] [Fintype C]
    (a : T → C) (b : C → ℕ) (hb : ∀ c, ((Finset.univ : Finset T).filter (fun t ↦ a t = c)).card = b c)
    (F : C → ℝ) : (∑ t, F (a t)) = ∑ c, (b c : ℝ) * F c := by
  classical
  rw [← Fintype.sum_fiberwise' a F]
  apply Finset.sum_congr rfl
  intro c _
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_subtype, hb]

private theorem mme_recursive_region_parent_profile_concentration_allow_empty {half R : ℕ} {W : Type*} [Fintype W]
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ)
    (hmass : ∀ c, ∑ w, mu c w = m c.1 c.2 + m c.1 (complement (htotal c.1) c.2))
    (k : ℕ) (hk : 0 < k) (hkn : ∀ r, n r ≠ 0 → k ≤ n r) (hdiv : ∀ r c, k ∣ m r c)
    (eps : ℝ) (heps : 0 < eps) (a : Address half R parent n) (ha : a ∈ RecursiveXHash.target m) :
    (𝔼 f : {f : Position n → W // Useful (fullCell htotal a) mu f},
      if ¬ parentTypical htotal n m mu eps f.val then (1 : ℝ) else 0) ≤
      25 * R * (Fintype.card W : ℝ) ^ 2 / ((k : ℝ) * eps ^ 2) := by
  classical
  have hjoint : ∀ r c, RecursiveThinSplit.count (a r) c = m r c :=
    (Finset.mem_filter.mp ha).2
  have hfull (c : Cell half R parent) :
      Fintype.card {p : Position n // fullCell htotal a p = c} =
        m c.1 c.2 + m c.1 (complement (htotal c.1) c.2) := by
    rcases c with ⟨r,c⟩
    rw [full_cell_fiber, hjoint, hjoint]
  have hmassP (c : Cell half R parent) :
      ∑ w, mu c w = Fintype.card {p : Position n // fullCell htotal a p = c} :=
    (hmass c).trans (hfull c).symm
  let q (r : Fin R) (t : Fin (n r) × Fin 2) : Position n := ⟨r,t⟩
  have hq (r : Fin R) : Function.Injective (q r) := by
    intro t s h
    exact eq_of_heq (Sigma.mk.inj h).2
  have hsize (r : Fin R) (t : Fin (n r)) (h : Fin 2) :
      k ≤ Fintype.card {p : Position n // fullCell htotal a p = fullCell htotal a (q r (t,h))} := by
    let c := fullCell htotal a (q r (t,h))
    have hpos : 0 < Fintype.card {p : Position n // fullCell htotal a p = c} := by
      letI : Nonempty {p : Position n // fullCell htotal a p = c} := ⟨⟨q r (t,h),rfl⟩⟩
      exact Fintype.card_pos
    rw [hfull] at hpos ⊢
    exact Nat.le_of_dvd hpos (Nat.dvd_add (hdiv c.1 c.2) (hdiv c.1 (complement (htotal c.1) c.2)))
  have hcenter (r : Fin R) (w : Fin 2 → W) : parentMixture htotal n m mu r w =
      (∑ t : Fin (n r), ∏ h : Fin 2, ((mu (fullCell htotal a (q r (t,h))) (w h) : ℝ) /
        Fintype.card {p : Position n // fullCell htotal a p = fullCell htotal a (q r (t,h))})) / n r := by
    unfold parentMixture
    congr 1
    have hden (c : Cell half R parent) : Nat.card {z : Position n // fullCell htotal a z = c} =
        ∑ w, mu c w := by simpa only [Nat.card_eq_fintype_card] using (hmassP c).symm
    simp only [← Nat.card_eq_fintype_card]
    simp_rw [hden]
    simp only [Fin.prod_univ_two, q, fullCell, Fin.isValue, ↓reduceIte,
      show (1 : Fin 2) ≠ 0 by decide]
    have h := weighted_histogram (a r) (m r) (by
        intro c
        calc
          _ = RecursiveThinSplit.count (a r) c := by
            unfold RecursiveThinSplit.count
            apply congrArg Finset.card
            ext t
            simp
          _ = _ := hjoint r c)
      (fun c ↦ cellFrequency mu ⟨r,c⟩ (w 0) * cellFrequency mu ⟨r,complement (htotal r) c⟩ (w 1))
    simpa only [cellFrequency, mul_assoc] using h.symm
  have h := mme_prescribed_cell_parent_profile_concentration_allow_empty (fullCell htotal a) mu
    (by intro c; simpa only [← Nat.card_eq_fintype_card] using hmassP c) n q hq
    (parentMixture htotal n m mu)
    (by intro r w; simpa only [← Nat.card_eq_fintype_card] using hcenter r w) k hk hkn
    (by intro r t h; simpa only [← Nat.card_eq_fintype_card] using hsize r t h) eps heps
  simp only [parentTypical, not_forall, not_lt, q, Fintype.card_fin] at h ⊢
  convert h using 1
  apply Finset.expect_congr
  · ext f
    simp only [Finset.mem_univ]
  · intro f _
    simp only [← Nat.card_eq_fintype_card]


open BigOperators MME MME.RecursiveYZ MME.RegionRealization
open scoped Classical
set_option autoImplicit false

private theorem mme_recursive_region_derived_parent_hole_budget_allow_empty {half R ell : ℕ}
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (hmass : ∀ c, ∑ w, mu c w = m c.1 c.2 + m c.1 (complement (htotal c.1) c.2))
    (i : Fin 3) (hsupport : ∀ c w, 0 < mu c w → ∑ h, (w h).val = (c.2.val i).val)
    (k d : ℕ) (hk : 0 < k) (hkn : ∀ r, n r ≠ 0 → k ≤ n r) (hdiv : ∀ r c, k ∣ m r c)
    (eps : ℝ) (heps : 0 < eps)
    (hscale : (8 * d : ℝ) * (25 * R * (Fintype.card (CompleteSplit.CompleteWord ell) : ℝ) ^ 2) ≤
      (k : ℝ) * eps ^ 2)
    (a : Address half R parent n) (ha : a ∈ RecursiveXHash.target m) :
    8 * d * (typeHoles htotal i a mu (parentTypical htotal n m mu eps)).card ≤
      (unbrokenWords htotal i a mu).card := by
  classical
  have hgraded (f : Position n → CompleteSplit.CompleteWord ell)
      (hf : Useful (fullCell htotal a) mu f) : Graded htotal i a f := by
    intro p
    have hp : 0 < mu (fullCell htotal a p) (f p) := by
      rw [← hf]
      unfold count
      apply Finset.card_pos.mpr
      refine ⟨p, ?_⟩
      simp
    exact hsupport _ _ hp
  let U := {f : Position n → CompleteSplit.CompleteWord ell // Useful (fullCell htotal a) mu f}
  let H := {f : U // ¬ parentTypical htotal n m mu eps f.val}
  have hu : Fintype.card U = (unbrokenWords htotal i a mu).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext f
    simp only [unbrokenWords, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hf ↦ ⟨hgraded f hf,hf⟩,fun hf ↦ hf.2⟩
  have hh : Fintype.card H = (typeHoles htotal i a mu (parentTypical htotal n m mu eps)).card := by
    rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun f ↦ Useful (fullCell htotal a) mu f) (fun f ↦ ¬ parentTypical htotal n m mu eps f)),
      Fintype.card_subtype]
    congr 1
    ext f
    simp only [typeHoles, unbrokenWords, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h ↦ ⟨⟨hgraded f h.1,h.1⟩,h.2⟩,fun h ↦ ⟨h.1.2,h.2⟩⟩
  rw [← hh, ← hu]
  by_cases hd : d = 0
  · simp [hd]
  have hd' : (0 : ℝ) < 8 * d := by positivity
  by_cases hU : Fintype.card U = 0
  · have hH : Fintype.card H = 0 := Nat.eq_zero_of_le_zero (hU ▸ Fintype.card_subtype_le _)
    simp [hH]
  have hU' : (0 : ℝ) < Fintype.card U := by exact_mod_cast (Nat.pos_of_ne_zero hU)
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hden : (0 : ℝ) < (k : ℝ) * eps ^ 2 := by positivity
  have hprob := mme_recursive_region_parent_profile_concentration_allow_empty parent n htotal m mu hmass
    k hk hkn hdiv eps heps a ha
  have hmean : (𝔼 f : U, if ¬ parentTypical htotal n m mu eps f.val then (1 : ℝ) else 0) =
      (Fintype.card H : ℝ) / Fintype.card U := by
    rw [Fintype.expect_eq_sum_div_card]
    congr 1
    change (∑ f : {f : Position n → CompleteSplit.CompleteWord ell // Useful (fullCell htotal a) mu f},
      if ¬ parentTypical htotal n m mu eps f.val then (1 : ℝ) else 0) = (Fintype.card H : ℝ)
    simp only [H, U, Fintype.card_subtype, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hmean] at hprob
  have hsmall : 25 * R * (Fintype.card (CompleteSplit.CompleteWord ell) : ℝ) ^ 2 /
      ((k : ℝ) * eps ^ 2) ≤ 1 / (8 * d) := by
    apply (div_le_div_iff₀ hden hd').mpr
    simpa only [one_mul, mul_one, mul_comm] using hscale
  have h := (div_le_div_iff₀ hU' hd').mp (hprob.trans hsmall)
  have hf : (8 : ℝ) * d * Fintype.card H ≤ Fintype.card U := by nlinarith
  exact_mod_cast hf


open BigOperators MME MME.RecursiveYZ MME.RegionRealization MME.ProfiledCW
  MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells
open scoped Classical
private theorem mme_exact_step_source_refinement_on_unbroken
    {ell N : ℕ} {P Q : Predicate N} (E : ExactStep ell N P)
    (hPQ : ∀ j i f, f ∈ unbrokenWords E.stage.total i (E.address j) (E.stage.mu i) →
      P i (flatten E.stage.positions E.length f) →
      Q i (flatten E.stage.positions E.length f)) :
    ∃ F : ExactStep ell N Q, F.count = E.count ∧
      F.stage.repairExponent = E.stage.repairExponent ∧
      F.copies = E.copies ∧ F.output = E.output := by
  classical
  let F : ExactStep ell N Q := {
    hash := E.hash
    stage := E.stage
    level := E.level
    length := E.length
    count := E.count
    state := E.state
    address := E.address
    injective := E.injective
    target := E.target
    bucketed := E.bucketed
    hashed := E.hashed
    isolated := E.isolated
    holes := by
      intro j i
      apply le_trans _ (E.holes j i)
      apply Nat.mul_le_mul_left
      apply Finset.card_le_card
      apply Finset.union_subset_union
      · intro f hf
        obtain ⟨hf, hnot⟩ := Finset.mem_filter.mp hf
        exact Finset.mem_filter.mpr ⟨hf, fun hp => hnot (hPQ j i f hf hp)⟩
      · exact Finset.Subset.refl _ }
  exact ⟨F,rfl,rfl,rfl,rfl⟩

private theorem split_flatten {S : Type} {ell L M : ℕ} (positions : Fin L ≃ S)
    (length : L * 2 ^ (ell - 1) = M) (f : S → CompleteSplit.CompleteWord ell) :
    ProfiledCW.split positions length (ProfiledCW.flatten positions length f) = f := by
  funext p h
  simp [ProfiledCW.split, ProfiledCW.flatten]

/-- Exact regional extraction with the same count and repair bounds when some
regions are empty. Only nonempty regions need the minimum sample size. -/
theorem solution {half R ell N L M : ℕ}
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (hhalf : half = 2 * 2 ^ (ell - 1))
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r))
    (positions : Fin L ≃ Position n) (length : L * 2 ^ (ell - 1) = M)
    (mu : Fin 3 → Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (hmass : ∀ i c, ∑ w, mu i c w = m c.1 c.2 + m c.1 (complement (htotal c.1) c.2))
    (hsupport : ∀ i c w, 0 < mu i c w → ∑ h, (w h).val = (c.2.val i).val)
    (hboundary : BoundaryProfiles mu)
    (reference : Address half R parent n) (href : reference ∈ RecursiveXHash.target m)
    (k d : ℕ) (hk : 0 < k) (hd : 1 < d) (hkn : ∀ r, n r ≠ 0 → k ≤ n r) (hdiv : ∀ r c, k ∣ m r c)
    (eps : ℝ) (heps : 0 < eps)
    (hscale : (8 * d : ℝ) * (25 * R * (Fintype.card (CompleteSplit.CompleteWord ell) : ℝ) ^ 2) ≤
      (k : ℝ) * eps ^ 2)
    (source : Predicate M)
    (hsource : ∀ i (a : Address half R parent n), a ∈ RecursiveXHash.target m →
      ∀ f : Position n → CompleteSplit.CompleteWord ell,
        Graded htotal i a f → parentTypical htotal n m (mu i) eps f →
        source i (ProfiledCW.flatten positions length f)) :
    let keep := fun (i : Fin 2) (_ : Address half R parent n) ↦ parentTypical htotal n m (mu (yzMode i)) eps
    let Q := commonScale half (loadNum htotal m d (fun i ↦ mu (yzMode i)) keep) (loadDen m)
    let cap := ∏ i : Fin 3, Nat.card (Block ell (fullCell htotal reference) (fun c i ↦ (c.2.val i).val) mu i)
    ∃ E : ExactStep ell M source,
      ((RecursiveXHash.target (n := n) m).card : ℝ) * Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) ≤ E.count ∧
      E.stage.repairExponent = Nat.log d cap + 1 ∧
      E.output = fun i x ↦ Graded htotal i reference (ProfiledCW.split positions length x) ∧
        Useful (fullCell htotal reference) (mu i) (ProfiledCW.split positions length x) := by
  classical
  let P : Predicate M := fun i x ↦ parentTypical htotal n m (mu i) eps (ProfiledCW.split positions length x)
  let keep := fun (i : Fin 2) (_ : Address half R parent n) ↦ parentTypical htotal n m (mu (yzMode i)) eps
  let Q := commonScale half (loadNum htotal m d (fun i ↦ mu (yzMode i)) keep) (loadDen m)
  let cap := ∏ i : Fin 3, Nat.card (Block ell (fullCell htotal reference) (fun c i ↦ (c.2.val i).val) mu i)
  have htype (i : Fin 3) (a : Address half R parent n) (ha : a ∈ RecursiveXHash.target m) :
      8 * d * (typeHoles htotal i a (mu i) (parentTypical htotal n m (mu i) eps)).card ≤
        (unbrokenWords htotal i a (mu i)).card :=
    mme_recursive_region_derived_parent_hole_budget_allow_empty parent n htotal m (mu i) (hmass i) i (hsupport i)
      k d hk hkn hdiv eps heps hscale a ha
  obtain ⟨p,hprime,hodd,hgrade,hlow,hupp,S,hSr,hSf,state,I,hIt,hIb,hIh,hIu,hIso,hIc⟩ :=
    mme_recursive_region_computed_hash_selection parent n htotal m e d (fun i ↦ mu (yzMode i))
      (fun i ↦ hmass (yzMode i)) keep (fun i a ha ↦ htype (yzMode i) a ha)
  let D : HashExtraction.HashData := {
    half := half
    R := R
    parent := parent
    n := n
    m := m
    N := N
    p := p
    prime := hprime
    odd := hodd
    grade_lt := hgrade
    positions := e
    labels := S
    labels_range := hSr
    labels_free := hSf
    good := fun state ↦ usable htotal m e (S.image (fun a : ℕ ↦ (a : ZMod p))) state d
      (fun i ↦ mu (yzMode i)) keep }
  let A : Stage D := {
    ell := ell
    L := L
    repairScale := d
    repairExponent := Nat.log d cap + 1
    total := htotal
    half_eq := hhalf
    positions := positions
    mu := mu
    boundary := hboundary
    mass := hmass
    reference := reference
    reference_target := href
    keep := keep
    good_eq := fun _ ↦ rfl
    capacity := Nat.lt_pow_succ_log_self hd cap }
  let address (j : Fin I.card) : Address half R parent n := (I.equivFin.symm j).val
  have hj (j : Fin I.card) : address j ∈ I := (I.equivFin.symm j).property
  have haddr : Function.Injective address := Subtype.val_injective.comp I.equivFin.symm.injective
  have hsplit (i : Fin 3) (f : Position n → CompleteSplit.CompleteWord ell) :
      P i (ProfiledCW.flatten positions length f) = parentTypical htotal n m (mu i) eps f := by
    simp only [P, split_flatten]
  have hholes (j : Fin I.card) (i : Fin 3) :
      4 * d * (((unbrokenWords htotal i (address j) (mu i)).filter
          (fun f ↦ ¬ P i (ProfiledCW.flatten positions length f))) ∪
        (if i = 1 then filterHoles htotal m e (S.image (fun a : ℕ ↦ (a : ZMod p))) state 0 (mu 1) (address j) (keep 0 (address j))
         else if i = 2 then filterHoles htotal m e (S.image (fun a : ℕ ↦ (a : ZMod p))) state 1 (mu 2) (address j) (keep 1 (address j))
         else ∅)).card ≤ (unbrokenWords htotal i (address j) (mu i)).card := by
    have hu : ∀ i : Fin 2,
        4 * d * (filterHoles htotal m e (S.image (fun a : ℕ ↦ (a : ZMod p))) state i
          (mu (yzMode i)) (address j) (keep i (address j))).card ≤
            (unbrokenWords htotal (yzMode i) (address j) (mu (yzMode i))).card :=
      (Finset.mem_filter.mp (hIu (hj j))).2
    fin_cases i
    · have hh := htype 0 (address j) (hIt (hj j))
      have hsmall : 4 * d * (typeHoles htotal 0 (address j) (mu 0) (parentTypical htotal n m (mu 0) eps)).card ≤
          (unbrokenWords htotal 0 (address j) (mu 0)).card :=
        (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right d (by decide : 4 ≤ 8))).trans hh
      simpa [hsplit, typeHoles] using hsmall
    · simpa [hsplit, keep, yzMode, filterHoles, typeHoles, ← Finset.union_assoc] using hu 0
    · simpa [hsplit, keep, yzMode, filterHoles, typeHoles, ← Finset.union_assoc] using hu 1
  let E : ExactStep ell M P := {
    hash := D
    stage := A
    level := rfl
    length := length
    count := I.card
    state := state
    address := address
    injective := haddr
    target := fun j ↦ hIt (hj j)
    bucketed := fun j ↦ hIb (hj j)
    hashed := fun j ↦ hIh (hj j)
    isolated := fun j b hb he ↦ hIso (address j) (hj j) b hb he
    holes := hholes }
  have hincl : ∀ j i f,
      f ∈ unbrokenWords E.stage.total i (E.address j) (E.stage.mu i) →
      P i (ProfiledCW.flatten E.stage.positions E.length f) →
      source i (ProfiledCW.flatten E.stage.positions E.length f) := by
    intro j i f hf hp
    apply hsource i (address j) (hIt (hj j)) f
    · exact (Finset.mem_filter.mp hf).2.1
    · exact (hsplit i f).mp hp
  obtain ⟨F, hcount, hexponent, _, houtput⟩ :=
    mme_exact_step_source_refinement_on_unbroken E hincl
  refine ⟨F, ?_, ?_, ?_⟩
  · simpa only [hcount] using hIc
  · exact hexponent
  · exact houtput


open MME.ProfiledCW MME.RecursiveYZ.CWCells



#print axioms solution
