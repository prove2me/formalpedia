-- Prove2me | solution 1 for AdjSum.cycCount_gauss_congruence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T10:09:17.084506+00:00
-- url     : https://prove2.me/submissions/9d95752c-f3c5-48f6-8d86-ef9ab002a6f6

import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_GaussCongruence
import Definitions.Def_Applications_AdjacentSumPolytopes_Necklace
import Definitions.Def_Applications_AdjacentSumPolytopes_Recurrence

open Finset Function Matrix AdjSum

theorem e568_rot_pow_apply (s q : ℕ) (k : ℕ) (x : CycPt s q) (i : Fin (q + 1)) :
    ((rot s q ^ k) x).1 i = x.1 ⟨(i.val + k) % (q + 1), Nat.mod_lt _ (Nat.succ_pos q)⟩ := by
  induction k generalizing x with
  | zero =>
    show x.1 i = _
    refine congrArg x.1 (Fin.ext ?_)
    simp [Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    rw [pow_succ]
    show ((rot s q ^ k) (rot s q x)).1 i = _
    rw [ih]
    show x.1 (⟨(i.val + k) % (q + 1), _⟩ + 1) = _
    refine congrArg x.1 (Fin.ext ?_)
    rw [Fin.val_add, Fin.val_one']
    show ((i.val + k) % (q + 1) + 1 % (q + 1)) % (q + 1) = (i.val + (k + 1)) % (q + 1)
    rw [← Nat.add_mod, Nat.add_assoc]

theorem e568_hpow (s q : ℕ) (k : ℕ) (x : CycPt s q) :
    (rot s q ^ k) x = (rot s q)^[k] x := by
  induction k generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ]
    show (rot s q ^ m) ((rot s q) x) = (rot s q)^[m + 1] x
    rw [ih, Function.iterate_succ_apply]

theorem e568_periodic_mod (s q e : ℕ) (h : (e + 1) ∣ (q + 1)) (x : CycPt s q)
    (hx : (rot s q ^ (e + 1)) x = x) (i : Fin (q + 1)) :
    x.1 i = x.1 ⟨i.val % (e + 1), lt_of_lt_of_le (Nat.mod_lt _ (Nat.succ_pos e))
      (Nat.le_of_dvd (Nat.succ_pos q) h)⟩ := by
  have ht : ∀ t : ℕ, (rot s q ^ ((e + 1) * t)) x = x := by
    intro t
    rw [pow_mul]
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [pow_succ]
      show ((rot s q ^ (e + 1)) ^ t) ((rot s q ^ (e + 1)) x) = x
      rw [hx, ih]
  have := congrArg (fun y : CycPt s q => y.1 ⟨i.val % (e + 1), lt_of_lt_of_le
      (Nat.mod_lt _ (Nat.succ_pos e)) (Nat.le_of_dvd (Nat.succ_pos q) h)⟩) (ht (i.val / (e + 1)))
  simp only at this
  rw [e568_rot_pow_apply] at this
  rw [← this]
  refine congrArg x.1 (Fin.ext ?_)
  show i.val = (i.val % (e + 1) + (e + 1) * (i.val / (e + 1))) % (q + 1)
  rw [Nat.mod_add_div, Nat.mod_eq_of_lt i.isLt]

theorem e568_card_fix (s q e : ℕ) (h : (e + 1) ∣ (q + 1)) :
    (Finset.univ.filter (fun x : CycPt s q => (rot s q ^ (e + 1)) x = x)).card
      = cycCount s e := by
  classical
  have hle : e + 1 ≤ q + 1 := Nat.le_of_dvd (Nat.succ_pos q) h
  have hinj : Function.Injective (cycExt (s := s) h) := by
    intro y y' hyy
    apply Subtype.ext
    funext j
    have := congrArg (fun z : CycPt s q => z.1 ⟨j.val, by omega⟩) hyy
    simp only [cycExt] at this
    have hj : idx e j.val = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
    rwa [hj] at this
  have himg : Finset.univ.filter (fun x : CycPt s q => (rot s q ^ (e + 1)) x = x)
      = Finset.univ.image (cycExt (s := s) h) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hx
      have hP := e568_periodic_mod s q e h x hx
      refine ⟨⟨fun j => x.1 ⟨j.val, by omega⟩, ?_⟩, ?_⟩
      · rw [mem_cycSet]
        intro j
        have hx2 := (mem_cycSet.mp x.2) ⟨j.val, by omega⟩
        have key : x.1 (⟨j.val, by omega⟩ + 1) = x.1 ⟨(j + 1).val, lt_of_lt_of_le (j + 1).isLt hle⟩ := by
          rw [hP (⟨j.val, by omega⟩ + 1), hP ⟨(j + 1).val, lt_of_lt_of_le (j + 1).isLt hle⟩]
          refine congrArg x.1 (Fin.ext ?_)
          show ((⟨j.val, by omega⟩ + 1 : Fin (q + 1)).val) % (e + 1)
            = ((j + 1 : Fin (e + 1)).val) % (e + 1)
          rw [Fin.val_add, Fin.val_one', Fin.val_add, Fin.val_one', Nat.mod_mod_of_dvd _ h,
            add_one_mod_dvd h, Nat.mod_mod, add_one_mod_dvd (dvd_refl (e + 1))]
        rw [key] at hx2
        exact hx2
      · apply Subtype.ext
        funext i
        show x.1 ⟨(idx e i.val).val, _⟩ = x.1 i
        rw [hP i]
        rfl
    · rintro ⟨y, -, rfl⟩
      apply Subtype.ext
      funext i
      rw [e568_rot_pow_apply]
      show y.1 (idx e _) = y.1 (idx e i.val)
      refine congrArg y.1 (Fin.ext ?_)
      show ((i.val + (e + 1)) % (q + 1)) % (e + 1) = i.val % (e + 1)
      rw [Nat.mod_mod_of_dvd _ h, Nat.add_mod_right]
  rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  simp [cycCount]

theorem e568_sum_divisors (s q d : ℕ) (hd : d ∣ q + 1) (hd0 : 0 < d) :
    ∑ i ∈ d.divisors,
      ((Finset.univ.filter (fun x : CycPt s q => minimalPeriod (rot s q) x = i)).card : ℤ)
      = (cycCount s (d - 1) : ℤ) := by
  classical
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [Nat.add_sub_cancel, ← e568_card_fix s q e hd, ← Nat.cast_sum]
  congr 1
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => minimalPeriod (rot s q) x)
    (t := (e + 1).divisors)]
  · apply Finset.sum_congr rfl
    intro i hi
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      refine ⟨?_, hx⟩
      rw [e568_hpow]
      have : minimalPeriod (rot s q) x ∣ e + 1 := by
        rw [hx]
        exact Nat.dvd_of_mem_divisors hi
      exact (Function.isPeriodicPt_iff_minimalPeriod_dvd.mpr this)
    · rintro ⟨-, hx⟩
      exact hx
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx
    rw [e568_hpow] at hx
    have := Function.isPeriodicPt_iff_minimalPeriod_dvd.mp hx
    simp only [Finset.mem_coe, Nat.mem_divisors]
    exact ⟨this, by omega⟩

theorem e568_aper_dvd (s q : ℕ) :
    (q + 1) ∣ (Finset.univ.filter
      (fun x : CycPt s q => Function.minimalPeriod (rot s q) x = q + 1)).card := by
  classical
  set f : CycPt s q → CycPt s q := rot s q with hf
  have hper : ∀ x : CycPt s q, f^[q + 1] x = x := by
    intro x
    rw [hf, ← e568_hpow]
    refine Subtype.ext ?_
    funext i
    rw [e568_rot_pow_apply]
    refine congrArg x.1 (Fin.ext ?_)
    simp [Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
  have hmem : ∀ x : CycPt s q, x ∈ Function.periodicPts f := by
    intro x
    exact ⟨q + 1, by omega, hper x⟩
  set S : Finset (CycPt s q) :=
    Finset.univ.filter (fun x => Function.minimalPeriod f x = q + 1) with hS
  set orb : CycPt s q → Finset (CycPt s q) :=
    fun x => (Finset.range (q + 1)).image (fun k => f^[k] x) with horb
  have hcard : ∀ x ∈ S, (orb x).card = q + 1 := by
    intro x hx
    rw [hS, Finset.mem_filter] at hx
    rw [horb]
    rw [Finset.card_image_of_injOn, Finset.card_range]
    have hinj := Function.iterate_injOn_Iio_minimalPeriod (f := f) (x := x)
    rw [hx.2] at hinj
    intro a ha b hb hab
    exact hinj (by simpa using ha) (by simpa using hb) hab
  have hmemorb : ∀ x : CycPt s q, x ∈ orb x := by
    intro x
    rw [horb]
    exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩
  have hsub : ∀ x ∈ S, ∀ z ∈ orb x, z ∈ S ∧ orb z ⊆ orb x := by
    intro x hxS z hz
    rw [horb, Finset.mem_image] at hz
    obtain ⟨k, -, rfl⟩ := hz
    rw [hS, Finset.mem_filter] at hxS
    constructor
    · rw [hS, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by
        rw [Function.minimalPeriod_apply_iterate (hmem x) k, hxS.2]⟩
    · intro w hw
      rw [horb, Finset.mem_image] at hw
      obtain ⟨j, -, rfl⟩ := hw
      rw [horb, Finset.mem_image]
      refine ⟨(j + k) % (q + 1), Finset.mem_range.mpr (Nat.mod_lt _ (by omega)), ?_⟩
      rw [← Function.iterate_add_apply]
      exact (Function.IsPeriodicPt.iterate_mod_apply (hper x) (j + k))
  have hfib : ∀ x ∈ S, S.filter (fun y => orb y = orb x) = orb x := by
    intro x hxS
    refine Finset.Subset.antisymm ?_ ?_
    · intro y hy
      rw [Finset.mem_filter] at hy
      rw [← hy.2]
      exact hmemorb y
    · intro z hz
      obtain ⟨hzS, hzsub⟩ := hsub x hxS z hz
      rw [Finset.mem_filter]
      refine ⟨hzS, ?_⟩
      exact Finset.eq_of_subset_of_card_le hzsub (by rw [hcard x hxS, hcard z hzS])
  have hfw := Finset.card_eq_sum_card_fiberwise
    (f := orb) (s := S) (t := S.image orb) (fun x hx => Finset.mem_image_of_mem orb hx)
  rw [hfw]
  refine Finset.dvd_sum ?_
  intro b hb
  obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hb
  rw [hfib x hxS, hcard x hxS]

set_option maxHeartbeats 4000000 in
open Finset Function Matrix AdjSum in
theorem solution (s q : ℕ) :
    ((q + 1 : ℕ) : ℤ) ∣ ∑ x ∈ (q + 1).divisorsAntidiagonal,
      (ArithmeticFunction.moebius x.1 : ℤ) * (cycCount s (x.2 - 1) : ℤ) := by
  classical
  have hmob := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on (R := ℤ)
      (f := fun d => ((Finset.univ.filter
        (fun x : CycPt s q => minimalPeriod (rot s q) x = d)).card : ℤ))
      (g := fun d => (cycCount s (d - 1) : ℤ)) {d | d ∣ q + 1}
      (fun m n hmn hn => dvd_trans hmn hn)).mp
      (fun d hd hdq => e568_sum_divisors s q d hdq hd) (q + 1) (by omega) (dvd_refl _)
  simp only [Int.cast_id] at hmob
  rw [hmob]
  exact_mod_cast e568_aper_dvd s q
