-- Prove2me | solution 1 for mme_released_positive_region_position_transport
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-24T01:55:05.763904+00:00
-- url     : https://prove2.me/submissions/d43ef713-e63c-47b6-9887-e64b6f526066

import Theorems.Thm_mme_released_positive_region0_profile_reindex
import Theorems.Thm_mme_released_positive_region1_profile_reindex
import Theorems.Thm_mme_released_positive_region2_profile_reindex
import Theorems.Thm_mme_released_positive_region3_profile_reindex
import Theorems.Thm_mme_released_positive_region4_profile_reindex
import Theorems.Thm_mme_released_positive_region5_profile_reindex
import Mathlib.Tactic.FinCases
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_released_joint_interior_frame
import Definitions.Def_mme_graded_integer_regional_step_data
import Mathlib.Data.Fintype.EquivFin
import Mathlib.SetTheory.Cardinal.Finite

open scoped BigOperators
open scoped Classical
open MME MME.RecursiveYZ MME.RegionRealization MME.CompleteSplit
set_option autoImplicit false

namespace PositivePositionTransport

def positionMap {R S : ℕ} {keep : Fin R → Prop}
    {n : Fin R → ℕ} {n' : Fin S → ℕ}
    (e : Fin S ≃ {j : Fin R // keep j})
    (hn : ∀ r, n' r = n (e r).val) : Position n' → Position n :=
  fun p => ⟨(e p.1).val, Fin.cast (hn p.1) p.2.1, p.2.2⟩

theorem positionMap_bijective {R S : ℕ} {keep : Fin R → Prop}
    {n : Fin R → ℕ} {n' : Fin S → ℕ}
    (e : Fin S ≃ {j : Fin R // keep j})
    (hn : ∀ r, n' r = n (e r).val)
    (hz : ∀ j, ¬ keep j → n j = 0) : Function.Bijective (positionMap e hn) := by
  classical
  constructor
  · rintro ⟨r,t,h⟩ ⟨s,u,g⟩ heq
    have hrs : r = s := e.injective (Subtype.ext (congrArg Sigma.fst heq))
    subst s
    have htu : t = u := Fin.ext (congrArg (fun p : Position n => p.2.1.val) heq)
    have hhg : h = g := congrArg (fun p : Position n => p.2.2) heq
    subst u
    subst g
    rfl
  · rintro ⟨j,t,h⟩
    have hj : keep j := by
      by_contra hnot
      have ht := t.isLt
      have hzj := hz j hnot
      omega
    obtain ⟨r, hr⟩ := e.surjective ⟨j,hj⟩
    have hjr : (e r).val = j := congrArg Subtype.val hr
    subst j
    refine ⟨⟨r, Fin.cast (hn r).symm t, h⟩, ?_⟩
    simp [positionMap]

noncomputable def positionEquiv {R S : ℕ} {keep : Fin R → Prop}
    {n : Fin R → ℕ} {n' : Fin S → ℕ}
    (e : Fin S ≃ {j : Fin R // keep j})
    (hn : ∀ r, n' r = n (e r).val)
    (hz : ∀ j, ¬ keep j → n j = 0) : Position n' ≃ Position n :=
  Equiv.ofBijective (positionMap e hn) (positionMap_bijective e hn hz)

@[simp] theorem positionEquiv_apply {R S : ℕ} {keep : Fin R → Prop}
    {n : Fin R → ℕ} {n' : Fin S → ℕ}
    (e : Fin S ≃ {j : Fin R // keep j})
    (hn : ∀ r, n' r = n (e r).val)
    (hz : ∀ j, ¬ keep j → n j = 0)
    (r : Fin S) (t : Fin (n' r)) (h : Fin 2) :
    positionEquiv e hn hz ⟨r,t,h⟩ = ⟨(e r).val, Fin.cast (hn r) t, h⟩ := rfl

theorem split_positionEquiv {A B : Type} {ell L N : ℕ}
    (q : A ≃ B) (positions : Fin L ≃ B) (length : L * 2 ^ (ell - 1) = N)
    (x : ProfiledCW.FineWord N) (p : A) :
    ProfiledCW.split (positions.trans q.symm) length x p =
      ProfiledCW.split positions length x (q p) := rfl

theorem parentGraded_iff {R S ell : ℕ} {keep : Fin R → Prop}
    {n : Fin R → ℕ} {n' : Fin S → ℕ}
    {parent : Fin R → Fin 3 → ℕ} {parent' : Fin S → Fin 3 → ℕ}
    (e : Fin S ≃ {j : Fin R // keep j})
    (hn : ∀ r, n' r = n (e r).val)
    (hz : ∀ j, ¬ keep j → n j = 0)
    (hp : ∀ r, parent' r = parent (e r).val)
    (i : Fin 3) (f : Position n → CompleteWord ell) :
    ParentGraded parent' n' i (fun p => f (positionEquiv e hn hz p)) ↔
      ParentGraded parent n i f := by
  classical
  constructor
  · intro hg j t
    have hj : keep j := by
      by_contra hnot
      have ht := t.isLt
      have hzj := hz j hnot
      omega
    obtain ⟨r, hr⟩ := e.surjective ⟨j,hj⟩
    have hjr : (e r).val = j := congrArg Subtype.val hr
    subst j
    simpa [hp r] using hg r (Fin.cast (hn r).symm t)
  · intro hg r t
    simpa [hp r] using hg (e r).val (Fin.cast (hn r) t)

def splitEquiv {half : ℕ} {p q : Fin 3 → ℕ} (hp : p = q) :
    RecursiveThinSplit.Split half p ≃ RecursiveThinSplit.Split half q :=
  Equiv.cast (congrArg (RecursiveThinSplit.Split half) hp)

@[simp] theorem splitEquiv_apply {half : ℕ} {p q : Fin 3 → ℕ} (hp : p = q)
    (c : RecursiveThinSplit.Split half p) :
    splitEquiv hp c = Eq.mp (congrArg (RecursiveThinSplit.Split half) hp) c := rfl

theorem splitEquiv_complement {half : ℕ} {p q : Fin 3 → ℕ} (hp : p = q)
    (ht : p 0 + p 1 + p 2 = 2 * half) (ht' : q 0 + q 1 + q 2 = 2 * half)
    (c : RecursiveThinSplit.Split half p) :
    splitEquiv hp (complement ht c) = complement ht' (splitEquiv hp c) := by
  cases hp
  rfl

theorem cellFrequency_congr {C D W : Type} [Fintype W]
    (mu : C → W → ℕ) (mu' : D → W → ℕ) (c : C) (d : D)
    (hmu : ∀ w, mu c w = mu' d w) (w : W) :
    cellFrequency mu c w = cellFrequency mu' d w := by
  simp only [cellFrequency, hmu]

theorem parentMixture_congr {R S half : ℕ} {W : Type} [Fintype W]
    {parent : Fin R → Fin 3 → ℕ} {parent' : Fin S → Fin 3 → ℕ}
    (ht : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (ht' : ∀ r, parent' r 0 + parent' r 1 + parent' r 2 = 2 * half)
    (n : Fin R → ℕ) (n' : Fin S → ℕ)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (m' : ∀ r, RecursiveThinSplit.Split half (parent' r) → ℕ)
    (mu : Cell half R parent → W → ℕ) (mu' : Cell half S parent' → W → ℕ)
    (r : Fin S) (j : Fin R) (hp : parent' r = parent j)
    (hn : n' r = n j)
    (hm : ∀ c, m' r c = m j (splitEquiv hp c))
    (hmu : ∀ c w, mu' ⟨r,c⟩ w = mu ⟨j,splitEquiv hp c⟩ w)
    (w : Fin 2 → W) :
    parentMixture ht' n' m' mu' r w = parentMixture ht n m mu j w := by
  classical
  unfold parentMixture
  rw [hn]
  congr 1
  calc
    _ = ∑ c, (m j (splitEquiv hp c) : ℝ) *
        cellFrequency mu ⟨j,splitEquiv hp c⟩ (w 0) *
        cellFrequency mu ⟨j,complement (ht j) (splitEquiv hp c)⟩ (w 1) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [hm c, cellFrequency_congr mu' mu ⟨r,c⟩ ⟨j,splitEquiv hp c⟩ (hmu c)]
      rw [cellFrequency_congr mu' mu ⟨r,complement (ht' r) c⟩
        ⟨j,splitEquiv hp (complement (ht' r) c)⟩ (hmu _)]
      rw [splitEquiv_complement hp (ht' r) (ht j)]
    _ = _ := Equiv.sum_comp (splitEquiv hp)
      (fun c => (m j c : ℝ) * cellFrequency mu ⟨j,c⟩ (w 0) *
        cellFrequency mu ⟨j,complement (ht j) c⟩ (w 1))

theorem pairCount_cast {R S : ℕ} {W : Type} {n : Fin R → ℕ} {n' : Fin S → ℕ}
    (r : Fin S) (j : Fin R) (hn : n' r = n j)
    (f : Position n → W) (w : Fin 2 → W) :
    Nat.card {t : Fin (n' r) // ∀ h, f ⟨j,Fin.cast hn t,h⟩ = w h} =
      Nat.card {t : Fin (n j) // ∀ h, f ⟨j,t,h⟩ = w h} := by
  classical
  exact Nat.card_congr (Equiv.subtypeEquiv (finCongr hn) (fun _ => Iff.rfl))

theorem parentTypical_iff {R S half : ℕ} {W : Type} [Fintype W]
    {keep : Fin R → Prop} {n : Fin R → ℕ} {n' : Fin S → ℕ}
    {parent : Fin R → Fin 3 → ℕ} {parent' : Fin S → Fin 3 → ℕ}
    (ht : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (ht' : ∀ r, parent' r 0 + parent' r 1 + parent' r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (m' : ∀ r, RecursiveThinSplit.Split half (parent' r) → ℕ)
    (mu : Cell half R parent → W → ℕ) (mu' : Cell half S parent' → W → ℕ)
    (e : Fin S ≃ {j : Fin R // keep j})
    (hn : ∀ r, n' r = n (e r).val)
    (hz : ∀ j, ¬ keep j → n j = 0)
    (hp : ∀ r, parent' r = parent (e r).val)
    (hm : ∀ r c, m' r c = m (e r).val (splitEquiv (hp r) c))
    (hmu : ∀ r c w, mu' ⟨r,c⟩ w = mu ⟨(e r).val,splitEquiv (hp r) c⟩ w)
    (eps : ℝ) (heps : 0 < eps) (f : Position n → W) :
    parentTypical ht' n' m' mu' eps (fun p => f (positionEquiv e hn hz p)) ↔
      parentTypical ht n m mu eps f := by
  classical
  have hrow (r : Fin S) (w : Fin 2 → W) :
      |(Fintype.card {t : Fin (n' r) // ∀ h,
          f (positionEquiv e hn hz ⟨r,t,h⟩) = w h} : ℝ) / n' r -
          parentMixture ht' n' m' mu' r w| =
      |(Fintype.card {t : Fin (n (e r).val) // ∀ h,
          f ⟨(e r).val,t,h⟩ = w h} : ℝ) / n (e r).val -
          parentMixture ht n m mu (e r).val w| := by
    simp only [positionEquiv_apply, Fintype.card_eq_nat_card]
    rw [pairCount_cast (n := n) (n' := n') r (e r).val (hn r) f w, hn r]
    rw [parentMixture_congr ht ht' n n' m m' mu mu' r (e r).val
      (hp r) (hn r) (hm r) (hmu r)]
  constructor
  · intro htyp j w
    by_cases hj : keep j
    · obtain ⟨r, hr⟩ := e.surjective ⟨j,hj⟩
      have hjr : (e r).val = j := congrArg Subtype.val hr
      subst j
      have he := htyp r w
      rw [hrow r w] at he
      exact he
    · simp [parentMixture, hz j hj, heps]
  · intro htyp r w
    rw [hrow r w]
    exact htyp (e r).val w

/-- Package the coordinate and predicate transports while all count functions
remain abstract. Concrete tables are supplied only after this proof is checked. -/
theorem transport_band {R S half ell L N : ℕ}
    {keep : Fin R → Prop} {n : Fin R → ℕ} {n' : Fin S → ℕ}
    {parent : Fin R → Fin 3 → ℕ} {parent' : Fin S → Fin 3 → ℕ}
    (ht : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (ht' : ∀ r, parent' r 0 + parent' r 1 + parent' r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (m' : ∀ r, RecursiveThinSplit.Split half (parent' r) → ℕ)
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ)
    (mu' : Fin 3 → Cell half S parent' → CompleteWord ell → ℕ)
    (e : Fin S ≃ {j : Fin R // keep j})
    (hn : ∀ r, n' r = n (e r).val)
    (hz : ∀ j, ¬ keep j → n j = 0)
    (hp : ∀ r, parent' r = parent (e r).val)
    (hm : ∀ r c, m' r c = m (e r).val (splitEquiv (hp r) c))
    (hmu : ∀ i r c w, mu' i ⟨r,c⟩ w = mu i ⟨(e r).val,splitEquiv (hp r) c⟩ w)
    (positions : Fin L ≃ Position n) (length : L * 2 ^ (ell - 1) = N) :
    ∃ q : Position n' ≃ Position n,
      (∀ (r : Fin S) (t : Fin (n' r)) (h : Fin 2),
        (q ⟨r,t,h⟩).1 = (e r).val ∧
        (q ⟨r,t,h⟩).2.1.val = t.val ∧ (q ⟨r,t,h⟩).2.2 = h) ∧
      let compactPositions := positions.trans q.symm
      (∀ (x : ProfiledCW.FineWord N) (p : Position n'),
        ProfiledCW.split compactPositions length x p =
          ProfiledCW.split positions length x (q p)) ∧
      (∀ (i : Fin 3) (x : ProfiledCW.FineWord N),
        ParentGraded parent' n' i (ProfiledCW.split compactPositions length x) ↔
          ParentGraded parent n i (ProfiledCW.split positions length x)) ∧
      (∀ (eps : ℝ), 0 < eps → ∀ (i : Fin 3) (x : ProfiledCW.FineWord N),
        parentTypical ht' n' m' (mu' i) eps (ProfiledCW.split compactPositions length x) ↔
          parentTypical ht n m (mu i) eps (ProfiledCW.split positions length x)) := by
  let q := positionEquiv e hn hz
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · intro r t h
    exact ⟨rfl, rfl, rfl⟩
  · intro x p
    exact split_positionEquiv q positions length x p
  · intro i x
    exact parentGraded_iff e hn hz hp i (ProfiledCW.split positions length x)
  · intro eps heps i x
    exact parentTypical_iff ht ht' m m' (mu i) (mu' i) e hn hz hp hm (hmu i)
      eps heps (ProfiledCW.split positions length x)

end PositivePositionTransport

open MME.ReleasedJointInterior

namespace PositivePositionTransport

/-- Objective integer-data equalities suffice to transport the complete band.
This auxiliary is not a proposed conditional publication. -/
theorem transport_from_counts (region : Fin 6) (k : ℕ)
    (e : Fin 88 ≃ {j : Fin 270 // 0 < ReleasedJointInterior.size region 1 j})
    (hp : ∀ r, RecStage.parent3 region r = ReleasedJointInterior.parent region (e r).val)
    (hn0 : ∀ r, ReleasedJointInterior.size region k (e r).val = k * RecStage.n3 region r)
    (hm0 : ∀ (r : Fin 88) (c : RecursiveThinSplit.Split 4 (RecStage.parent3 region r)),
      ReleasedJointInterior.splitCount region k (e r).val
        (Eq.mp (congrArg (RecursiveThinSplit.Split 4) (hp r)) c) = k * RecStage.m3 region r c)
    (hmu0 : ∀ (i : Fin 3) (r : Fin 88)
      (c : RecursiveThinSplit.Split 4 (RecStage.parent3 region r)) (w : CompleteWord 2),
      ReleasedJointInterior.integerProfile region k i
        ⟨(e r).val, Eq.mp (congrArg (RecursiveThinSplit.Split 4) (hp r)) c⟩ w =
          k * RecStage.mu3 region i ⟨r,c⟩ w) :
    ∃ (e : Fin 88 ≃ {j : Fin 270 // 0 < size region 1 j})
      (q : Position (fun r => k * RecStage.n3 region r) ≃ Position (size region k)),
      (∀ r, RecStage.parent3 region r = parent region (e r).val) ∧
      (∀ (r : Fin 88) (t : Fin (k * RecStage.n3 region r)) (h : Fin 2),
        (q ⟨r,t,h⟩).1 = (e r).val ∧
        (q ⟨r,t,h⟩).2.1.val = t.val ∧ (q ⟨r,t,h⟩).2.2 = h) ∧
      let compactPositions := (positions region k).trans q.symm
      (∀ (x : ProfiledCW.FineWord (blocks region k * 4))
        (p : Position (fun r => k * RecStage.n3 region r)),
        ProfiledCW.split compactPositions (positions_length region k) x p =
          ProfiledCW.split (positions region k) (positions_length region k) x (q p)) ∧
      (∀ (i : Fin 3) (x : ProfiledCW.FineWord (blocks region k * 4)),
        ParentGraded (RecStage.parent3 region) (fun r => k * RecStage.n3 region r) i
          (ProfiledCW.split compactPositions (positions_length region k) x) ↔
        ParentGraded (parent region) (size region k) i
          (ProfiledCW.split (positions region k) (positions_length region k) x)) ∧
      (∀ (eps : ℝ), 0 < eps →
        ∀ (i : Fin 3) (x : ProfiledCW.FineWord (blocks region k * 4)),
          parentTypical (RecStage.htotal3 region) (fun r => k * RecStage.n3 region r)
            (fun r c => k * RecStage.m3 region r c)
            (fun c w => k * RecStage.mu3 region i c w) eps
            (ProfiledCW.split compactPositions (positions_length region k) x) ↔
          source region k eps i x) := by
  let hn : ∀ r, k * RecStage.n3 region r = ReleasedJointInterior.size region k (e r).val :=
    fun r => (hn0 r).symm
  have hz : ∀ j, ¬ 0 < ReleasedJointInterior.size region 1 j →
      ReleasedJointInterior.size region k j = 0 := by
    intro j hj
    have hscale : ReleasedJointInterior.size region k j =
        k * ReleasedJointInterior.size region 1 j := by
      simp [ReleasedJointInterior.size, Nat.mul_assoc]
    rw [hscale, Nat.eq_zero_of_not_pos hj, Nat.mul_zero]
  have hm : ∀ r c, k * RecStage.m3 region r c =
      ReleasedJointInterior.splitCount region k (e r).val (splitEquiv (hp r) c) := by
    intro r c
    simpa only [splitEquiv_apply] using (hm0 r c).symm
  have hmu : ∀ i r c w, k * RecStage.mu3 region i ⟨r,c⟩ w =
      ReleasedJointInterior.integerProfile region k i ⟨(e r).val,splitEquiv (hp r) c⟩ w := by
    intro i r c w
    simpa only [splitEquiv_apply] using (hmu0 i r c w).symm
  obtain ⟨q, hcoordinates, hsplit, hgraded, htypical⟩ :=
    transport_band (ReleasedJointInterior.parent_total region) (RecStage.htotal3 region)
      (ReleasedJointInterior.splitCount region k) (fun r c => k * RecStage.m3 region r c)
      (ReleasedJointInterior.integerProfile region k) (fun i c w => k * RecStage.mu3 region i c w)
      e hn hz hp hm hmu (ReleasedJointInterior.positions region k)
      (ReleasedJointInterior.positions_length region k)
  exact ⟨e, q, hp, hcoordinates, hsplit, hgraded, htypical⟩

end PositivePositionTransport

namespace PositivePositionTransport

private theorem exact_profile_counts (region : Fin 6) :
    ∃ (e : Fin 88 ≃ {j : Fin 270 // 0 < ReleasedJointInterior.size region 1 j})
      (hparent : ∀ r, RecStage.parent3 region r = ReleasedJointInterior.parent region (e r).val),
      ∀ k : ℕ,
        (∀ r, ReleasedJointInterior.size region k (e r).val = k * RecStage.n3 region r) ∧
        (∀ (r : Fin 88) (c : RecursiveThinSplit.Split 4 (RecStage.parent3 region r)),
          ReleasedJointInterior.splitCount region k (e r).val
            (Eq.mp (congrArg (RecursiveThinSplit.Split 4) (hparent r)) c) =
              k * RecStage.m3 region r c) ∧
        (∀ (i : Fin 3) (r : Fin 88)
          (c : RecursiveThinSplit.Split 4 (RecStage.parent3 region r))
          (w : CompleteSplit.CompleteWord 2),
          ReleasedJointInterior.integerProfile region k i
            ⟨(e r).val, Eq.mp (congrArg (RecursiveThinSplit.Split 4) (hparent r)) c⟩ w =
              k * RecStage.mu3 region i ⟨r, c⟩ w) := by
  fin_cases region
  · exact mme_released_positive_region0_profile_reindex
  · exact mme_released_positive_region1_profile_reindex
  · exact mme_released_positive_region2_profile_reindex
  · exact mme_released_positive_region3_profile_reindex
  · exact mme_released_positive_region4_profile_reindex
  · exact mme_released_positive_region5_profile_reindex

end PositivePositionTransport

theorem solution
    (region : Fin 6) (k : ℕ) :
    ∃ (e : Fin 88 ≃ {j : Fin 270 // 0 < size region 1 j})
      (q : Position (fun r => k * RecStage.n3 region r) ≃ Position (size region k)),
      (∀ r, RecStage.parent3 region r = parent region (e r).val) ∧
      (∀ (r : Fin 88) (t : Fin (k * RecStage.n3 region r)) (h : Fin 2),
        (q ⟨r,t,h⟩).1 = (e r).val ∧
        (q ⟨r,t,h⟩).2.1.val = t.val ∧ (q ⟨r,t,h⟩).2.2 = h) ∧
      let compactPositions := (positions region k).trans q.symm
      (∀ (x : ProfiledCW.FineWord (blocks region k * 4))
        (p : Position (fun r => k * RecStage.n3 region r)),
        ProfiledCW.split compactPositions (positions_length region k) x p =
          ProfiledCW.split (positions region k) (positions_length region k) x (q p)) ∧
      (∀ (i : Fin 3) (x : ProfiledCW.FineWord (blocks region k * 4)),
        ParentGraded (RecStage.parent3 region) (fun r => k * RecStage.n3 region r) i
          (ProfiledCW.split compactPositions (positions_length region k) x) ↔
        ParentGraded (parent region) (size region k) i
          (ProfiledCW.split (positions region k) (positions_length region k) x)) ∧
      (∀ (eps : ℝ), 0 < eps →
        ∀ (i : Fin 3) (x : ProfiledCW.FineWord (blocks region k * 4)),
          parentTypical (RecStage.htotal3 region) (fun r => k * RecStage.n3 region r)
            (fun r c => k * RecStage.m3 region r c)
            (fun c w => k * RecStage.mu3 region i c w) eps
            (ProfiledCW.split compactPositions (positions_length region k) x) ↔
          source region k eps i x) := by
  obtain ⟨e, hp, hcounts⟩ := PositivePositionTransport.exact_profile_counts region
  obtain ⟨hn, hm, hmu⟩ := hcounts k
  exact PositivePositionTransport.transport_from_counts region k e hp hn hm hmu

#print axioms solution
