-- Prove2me | solution 1 for mme_recursive_region_parent_profile_concentration
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T17:26:25.707237+00:00
-- url     : https://prove2.me/submissions/1b46ee93-f0e4-409e-a3ab-167b297be049

import Definitions.Def_mme_recursive_region_parent_profiles
import Theorems.Thm_mme_prescribed_cell_parent_profile_concentration

open BigOperators MME MME.RecursiveYZ MME.RegionRealization
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1400000


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

theorem solution {half R : ℕ} {W : Type*} [Fintype W]
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Cell half R parent → W → ℕ)
    (hmass : ∀ c, ∑ w, mu c w = m c.1 c.2 + m c.1 (complement (htotal c.1) c.2))
    (k : ℕ) (hk : 0 < k) (hkn : ∀ r, k ≤ n r) (hdiv : ∀ r c, k ∣ m r c)
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
  have h := mme_prescribed_cell_parent_profile_concentration (fullCell htotal a) mu
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
