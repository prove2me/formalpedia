-- Prove2me | Definitions.Def_Geometry_PythagoreanHydra_BerggrenDescent
-- name    : Geometry_PythagoreanHydra_BerggrenDescent
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T12:26:42.253681+00:00
-- url     : https://prove2.me/theorems/cff0625f-8317-4097-bcb2-47aacb006d2d
-- title:
--   Aether Catalog definitions — Geometry_PythagoreanHydra_BerggrenDescent
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.PythagoreanHydra.BerggrenDescent`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/PythagoreanHydra/BerggrenDescent.lean by skeleton subtraction
import Mathlib

/-!
# The Berggren descent: a complete classification of the Berggren tree

This file develops, from scratch but following the naming of the catalog module
`Catalog/Bridges/BerggrenTrees/BerggrenPythagoreanCore.lean` (definitions `IsPythag`,
`bergA`, `bergB`, `bergC`, `invA`, `invB`, `invC`), the *descent* half of the Berggren
theory, which that module leaves open (its `parent_exists` is commented out there
because the required case analysis was missing).

The main results are:

* `PythHydra.parent` — a single, uniform **parent map** `(a,b,c) ↦ (|u|, |v|, 3c-2a-2b)`
  with `u = a + 2b - 2c`, `v = 2a + b - 2c`.
* `PythHydra.parent_eq_inv` — the parent map *is* one of the three inverse Berggren
  moves `invA`, `invB`, `invC`; which one is decided by the signs of `u` and `v`.
* `PythHydra.parent_isPPT`, `PythHydra.parent_hyp_lt` — the parent of a primitive
  triple is primitive, with strictly smaller hypotenuse: the descent is well-founded.
* `PythHydra.reach_iff_isPPT` — **classification**: the Berggren tree rooted at
  `(3,4,5)` consists of exactly the primitive Pythagorean triples with odd first leg.
* `PythHydra.decidableReach` — consequently membership in the Berggren tree is
  *decidable* (by an elementary arithmetic test), which is the negative answer to the
  "Matiyasevich phenomenon on the tree" front of the research mission.
-/

namespace PythHydra

/-- A triple `(a,b,c)` is Pythagorean if `a² + b² = c²`. -/
def IsPythag (a b c : ℤ) : Prop := a ^ 2 + b ^ 2 = c ^ 2

/-- Berggren child A. -/
def bergA (a b c : ℤ) : ℤ × ℤ × ℤ := (a - 2*b + 2*c, 2*a - b + 2*c, 2*a - 2*b + 3*c)

/-- Berggren child B. -/
def bergB (a b c : ℤ) : ℤ × ℤ × ℤ := (a + 2*b + 2*c, 2*a + b + 2*c, 2*a + 2*b + 3*c)

/-- Berggren child C. -/
def bergC (a b c : ℤ) : ℤ × ℤ × ℤ := (-a + 2*b + 2*c, -2*a + b + 2*c, -2*a + 2*b + 3*c)

@[simp] theorem bergA_fst (a b c : ℤ) : (bergA a b c).1 = a - 2*b + 2*c := rfl
@[simp] theorem bergA_snd_fst (a b c : ℤ) : (bergA a b c).2.1 = 2*a - b + 2*c := rfl
@[simp] theorem bergA_snd_snd (a b c : ℤ) : (bergA a b c).2.2 = 2*a - 2*b + 3*c := rfl

@[simp] theorem bergB_fst (a b c : ℤ) : (bergB a b c).1 = a + 2*b + 2*c := rfl
@[simp] theorem bergB_snd_fst (a b c : ℤ) : (bergB a b c).2.1 = 2*a + b + 2*c := rfl
@[simp] theorem bergB_snd_snd (a b c : ℤ) : (bergB a b c).2.2 = 2*a + 2*b + 3*c := rfl

@[simp] theorem bergC_fst (a b c : ℤ) : (bergC a b c).1 = -a + 2*b + 2*c := rfl
@[simp] theorem bergC_snd_fst (a b c : ℤ) : (bergC a b c).2.1 = -2*a + b + 2*c := rfl
@[simp] theorem bergC_snd_snd (a b c : ℤ) : (bergC a b c).2.2 = -2*a + 2*b + 3*c := rfl

/-- Inverse Berggren move A. -/
def invA (a b c : ℤ) : ℤ × ℤ × ℤ := (a + 2*b - 2*c, -2*a - b + 2*c, -2*a - 2*b + 3*c)

/-- Inverse Berggren move B. -/
def invB (a b c : ℤ) : ℤ × ℤ × ℤ := (a + 2*b - 2*c, 2*a + b - 2*c, -2*a - 2*b + 3*c)

/-- Inverse Berggren move C. -/
def invC (a b c : ℤ) : ℤ × ℤ × ℤ := (-a - 2*b + 2*c, 2*a + b - 2*c, -2*a - 2*b + 3*c)




/-- A *primitive Pythagorean triple in Berggren normal form*: positive, coprime legs,
odd leg first.  This is exactly the shape of triples occurring in the Berggren tree. -/
structure IsPPT (a b c : ℤ) : Prop where
  ha : 0 < a
  hb : 0 < b
  hc : 0 < c
  pyth : IsPythag a b c
  cop : Int.gcd a b = 1
  odd : Odd a

/-! ### Elementary consequences of primitivity -/

theorem dvd_hyp_of_dvd_legs {a b c d : ℤ} (h : IsPythag a b c) (ha : d ∣ a) (hb : d ∣ b) :
    d ∣ c := by
  obtain ⟨k₁, rfl⟩ := ha
  obtain ⟨k₂, rfl⟩ := hb
  exact Int.pow_dvd_pow_iff two_ne_zero |>.1 ⟨k₁ ^ 2 + k₂ ^ 2, by linarith! [h.symm]⟩

/-- If the legs of a Pythagorean triple `(a',b',c')` generate, by fixed integer
combinations, the legs of a primitive triple `(a,b,·)`, then `(a',b')` is coprime too.
This is the uniform coprimality transfer used in both directions of the tree. -/
theorem cop_of_combination {a b a' b' c' : ℤ} (hp : IsPythag a' b' c')
    (hcop : Int.gcd a b = 1) (p q r s t w : ℤ)
    (hae : a = p * a' + q * b' + r * c') (hbe : b = s * a' + t * b' + w * c') :
    Int.gcd a' b' = 1 := by
  have hda : ((Int.gcd a' b' : ℕ) : ℤ) ∣ a' := Int.gcd_dvd_left a' b'
  have hdb : ((Int.gcd a' b' : ℕ) : ℤ) ∣ b' := Int.gcd_dvd_right a' b'
  have hdc : ((Int.gcd a' b' : ℕ) : ℤ) ∣ c' := dvd_hyp_of_dvd_legs hp hda hdb
  have h1 : ((Int.gcd a' b' : ℕ) : ℤ) ∣ a := by
    rw [hae]
    exact dvd_add (dvd_add (Dvd.dvd.mul_left hda p) (Dvd.dvd.mul_left hdb q))
      (Dvd.dvd.mul_left hdc r)
  have h2 : ((Int.gcd a' b' : ℕ) : ℤ) ∣ b := by
    rw [hbe]
    exact dvd_add (dvd_add (Dvd.dvd.mul_left hda s) (Dvd.dvd.mul_left hdb t))
      (Dvd.dvd.mul_left hdc w)
  have h3 := Int.dvd_gcd h1 h2
  rw [hcop] at h3
  exact Nat.dvd_one.mp h3

theorem IsPPT.legs_lt {a b c : ℤ} (h : IsPPT a b c) : a < c ∧ b < c := by
  have hp := h.pyth
  unfold IsPythag at hp
  constructor <;> nlinarith [h.ha, h.hb, h.hc]



/-! ### The uniform parent map -/

/-- First inverse coordinate (up to sign). -/
def uu (a b c : ℤ) : ℤ := a + 2*b - 2*c

/-- Second inverse coordinate (up to sign). -/
def vv (a b c : ℤ) : ℤ := 2*a + b - 2*c

/-- The parent hypotenuse. -/
def hh (a b c : ℤ) : ℤ := 3*c - 2*a - 2*b




theorem uu_vv_pythag {a b c : ℤ} (h : IsPythag a b c) :
    IsPythag (uu a b c) (vv a b c) (hh a b c) := by
  unfold IsPythag uu vv hh at *
  linear_combination h

/-- The parent hypotenuse is positive. -/
theorem hh_pos {a b c : ℤ} (h : IsPPT a b c) : 0 < hh a b c := by
  have hp := h.pyth
  unfold IsPythag at hp
  unfold hh
  nlinarith [h.ha, h.hb, h.hc, sq_nonneg (3*c - 2*a - 2*b), sq_nonneg (a - b),
    mul_pos h.ha h.hb]

/-- The parent hypotenuse is strictly smaller: the descent decreases the hypotenuse. -/
theorem hh_lt {a b c : ℤ} (h : IsPPT a b c) : hh a b c < c := by
  have hp := h.pyth
  unfold IsPythag at hp
  unfold hh
  nlinarith [h.ha, h.hb, sq_nonneg (a + b - c), sq_nonneg (a - b)]

/-- `u` is odd, hence never zero. -/
theorem uu_ne_zero {a b c : ℤ} (h : IsPPT a b c) : uu a b c ≠ 0 := by
  have ha := h.odd
  rw [Int.odd_iff] at ha
  intro hcon
  unfold uu at hcon
  omega

/-- `v` vanishes only for the root triple `(3,4,5)`. -/
theorem vv_ne_zero {a b c : ℤ} (h : IsPPT a b c) (hc : 5 < c) : vv a b c ≠ 0 := by
  intro hcon
  unfold vv at hcon
  have hp := h.pyth
  unfold IsPythag at hp
  -- `2a + b = 2c` together with `a² + b² = c²` forces `3b = 4a`
  have h34 : 3 * b = 4 * a := by nlinarith [h.ha, h.hb, h.hc]
  -- hence `3 ∣ a`, and `a = 3t, b = 4t`, so primitivity forces `t = 1`
  have h3a : (3 : ℤ) ∣ a := by
    have : (3 : ℤ) ∣ 4 * a := ⟨b, h34.symm⟩
    omega
  obtain ⟨t, rfl⟩ := h3a
  have hbt : b = 4 * t := by linarith
  subst hbt
  have hcop := h.cop
  have hd : t.natAbs ∣ Int.gcd (3 * t) (4 * t) :=
    Nat.dvd_gcd (by rw [Int.natAbs_mul]; exact Dvd.intro_left _ rfl)
      (by rw [Int.natAbs_mul]; exact Dvd.intro_left _ rfl)
  rw [hcop] at hd
  have ht1 := Nat.dvd_one.mp hd
  have htpos : 0 < t := by nlinarith [h.ha]
  have : t = 1 := by omega
  subst this
  omega

/-- `u` and `v` are never both non-positive: some inverse Berggren move applies. -/
theorem uu_or_vv_pos {a b c : ℤ} (h : IsPPT a b c) : 0 < uu a b c ∨ 0 < vv a b c := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  unfold uu at h1
  unfold vv at h2
  have hp := h.pyth
  unfold IsPythag at hp
  nlinarith [h.ha, h.hb, h.hc, mul_pos h.ha h.hb]

/-- Coprimality of the parent legs. -/
theorem uu_vv_cop {a b c : ℤ} (h : IsPPT a b c) : Int.gcd (uu a b c) (vv a b c) = 1 :=
  cop_of_combination (uu_vv_pythag h.pyth) h.cop 1 2 2 2 1 2
    (by simp only [uu, vv, hh]; ring) (by simp only [uu, vv, hh]; ring)

/-- The **parent map** of the Berggren tree: a single formula covering all three
inverse moves. -/
def parent (a b c : ℤ) : ℤ × ℤ × ℤ := (|uu a b c|, |vv a b c|, hh a b c)

/-- The parent map is literally one of the three inverse Berggren moves. -/
theorem parent_eq_inv {a b c : ℤ} (h : IsPPT a b c) (hc : 5 < c) :
    parent a b c = invA a b c ∨ parent a b c = invB a b c ∨ parent a b c = invC a b c := by
  have hu := uu_ne_zero h
  have hv := vv_ne_zero h hc
  have hor := uu_or_vv_pos h
  unfold parent invA invB invC
  rcases lt_or_gt_of_ne hu with hu' | hu'
  · -- u < 0, so v > 0
    have hv' : 0 < vv a b c := by rcases hor with h' | h' <;> omega
    right; right
    have e1 : |uu a b c| = -uu a b c := abs_of_neg hu'
    have e2 : |vv a b c| = vv a b c := abs_of_pos hv'
    rw [e1, e2]
    simp only [uu, vv, hh, Prod.mk.injEq]
    and_intros <;> first | trivial | ring
  · rcases lt_or_gt_of_ne hv with hv' | hv'
    · left
      have e1 : |uu a b c| = uu a b c := abs_of_pos hu'
      have e2 : |vv a b c| = -vv a b c := abs_of_neg hv'
      rw [e1, e2]
      simp only [uu, vv, hh, Prod.mk.injEq]
      and_intros <;> first | trivial | ring
    · right; left
      have e1 : |uu a b c| = uu a b c := abs_of_pos hu'
      have e2 : |vv a b c| = vv a b c := abs_of_pos hv'
      rw [e1, e2]
      simp only [uu, vv, hh, Prod.mk.injEq]
      and_intros <;> first | trivial | ring

/-- The parent of a Berggren triple is again a Berggren triple. -/
theorem parent_isPPT {a b c : ℤ} (h : IsPPT a b c) (hc : 5 < c) :
    IsPPT (parent a b c).1 (parent a b c).2.1 (parent a b c).2.2 := by
  have hu := uu_ne_zero h
  have hv := vv_ne_zero h hc
  refine ⟨?_, ?_, hh_pos h, ?_, ?_, ?_⟩
  · exact abs_pos.mpr hu
  · exact abs_pos.mpr hv
  · have := uu_vv_pythag h.pyth
    unfold IsPythag at this ⊢
    simp only [parent, sq_abs]
    exact this
  · have := uu_vv_cop h
    simpa [parent, Int.gcd, Int.natAbs_abs] using this
  · have ha := h.odd
    rw [Int.odd_iff] at ha ⊢
    simp only [parent, uu]
    rcases abs_choice (a + 2*b - 2*c) with h' | h' <;> rw [h'] <;> omega

theorem parent_hyp_lt {a b c : ℤ} (h : IsPPT a b c) : (parent a b c).2.2 < c := hh_lt h

/-- The chopped triple is recovered from its parent by a *forward* Berggren move. -/
theorem child_of_parent {a b c : ℤ} (h : IsPPT a b c) (hc : 5 < c) :
    (a, b, c) = bergA (parent a b c).1 (parent a b c).2.1 (parent a b c).2.2 ∨
    (a, b, c) = bergB (parent a b c).1 (parent a b c).2.1 (parent a b c).2.2 ∨
    (a, b, c) = bergC (parent a b c).1 (parent a b c).2.1 (parent a b c).2.2 := by
  rcases parent_eq_inv h hc with he | he | he
  · left; rw [he]; simp only [bergA, invA, Prod.mk.injEq]; exact ⟨by ring, by ring, by ring⟩
  · right; left; rw [he]; simp only [bergB, invB, Prod.mk.injEq]
    exact ⟨by ring, by ring, by ring⟩
  · right; right; rw [he]; simp only [bergC, invC, Prod.mk.injEq]
    exact ⟨by ring, by ring, by ring⟩

/-! ### Forward moves preserve the class -/

theorem bergA_isPPT {a b c : ℤ} (h : IsPPT a b c) :
    IsPPT (bergA a b c).1 (bergA a b c).2.1 (bergA a b c).2.2 := by
  obtain ⟨hac, hbc⟩ := h.legs_lt
  refine ⟨by simp only [bergA_fst]; linarith [h.ha], by simp only [bergA_snd_fst]; linarith [h.ha, h.hb],
    by simp only [bergA_snd_snd]; linarith [h.ha, h.hc], ?_, ?_, ?_⟩
  · have := h.pyth
    unfold IsPythag at this ⊢
    simp only [bergA_fst, bergA_snd_fst, bergA_snd_snd]
    linear_combination this
  · refine cop_of_combination (a' := (bergA a b c).1) (b' := (bergA a b c).2.1)
      (c' := (bergA a b c).2.2) ?_ h.cop 1 2 (-2) (-2) (-1) 2 ?_ ?_
    · have := h.pyth
      unfold IsPythag at this ⊢
      simp only [bergA_fst, bergA_snd_fst, bergA_snd_snd]
      linear_combination this
    · simp only [bergA_fst, bergA_snd_fst, bergA_snd_snd]; ring
    · simp only [bergA_fst, bergA_snd_fst, bergA_snd_snd]; ring
  · have := h.odd
    rw [Int.odd_iff] at this ⊢
    simp only [bergA_fst]
    omega

theorem bergB_isPPT {a b c : ℤ} (h : IsPPT a b c) :
    IsPPT (bergB a b c).1 (bergB a b c).2.1 (bergB a b c).2.2 := by
  refine ⟨by simp only [bergB_fst]; linarith [h.ha, h.hb, h.hc],
    by simp only [bergB_snd_fst]; linarith [h.ha, h.hb, h.hc],
    by simp only [bergB_snd_snd]; linarith [h.ha, h.hb, h.hc], ?_, ?_, ?_⟩
  · have := h.pyth
    unfold IsPythag at this ⊢
    simp only [bergB_fst, bergB_snd_fst, bergB_snd_snd]
    linear_combination this
  · refine cop_of_combination (a' := (bergB a b c).1) (b' := (bergB a b c).2.1)
      (c' := (bergB a b c).2.2) ?_ h.cop 1 2 (-2) 2 1 (-2) ?_ ?_
    · have := h.pyth
      unfold IsPythag at this ⊢
      simp only [bergB_fst, bergB_snd_fst, bergB_snd_snd]
      linear_combination this
    · simp only [bergB_fst, bergB_snd_fst, bergB_snd_snd]; ring
    · simp only [bergB_fst, bergB_snd_fst, bergB_snd_snd]; ring
  · have := h.odd
    rw [Int.odd_iff] at this ⊢
    simp only [bergB_fst]
    omega

theorem bergC_isPPT {a b c : ℤ} (h : IsPPT a b c) :
    IsPPT (bergC a b c).1 (bergC a b c).2.1 (bergC a b c).2.2 := by
  obtain ⟨hac, hbc⟩ := h.legs_lt
  refine ⟨by simp only [bergC_fst]; linarith [h.hb], by simp only [bergC_snd_fst]; linarith [h.hb, h.hc],
    by simp only [bergC_snd_snd]; linarith [h.hb, h.hc], ?_, ?_, ?_⟩
  · have := h.pyth
    unfold IsPythag at this ⊢
    simp only [bergC_fst, bergC_snd_fst, bergC_snd_snd]
    linear_combination this
  · refine cop_of_combination (a' := (bergC a b c).1) (b' := (bergC a b c).2.1)
      (c' := (bergC a b c).2.2) ?_ h.cop (-1) (-2) 2 2 1 (-2) ?_ ?_
    · have := h.pyth
      unfold IsPythag at this ⊢
      simp only [bergC_fst, bergC_snd_fst, bergC_snd_snd]
      linear_combination this
    · simp only [bergC_fst, bergC_snd_fst, bergC_snd_snd]; ring
    · simp only [bergC_fst, bergC_snd_fst, bergC_snd_snd]; ring
  · have := h.odd
    rw [Int.odd_iff] at this ⊢
    simp only [bergC_fst]
    omega

/-! ### The Berggren tree and its classification -/

/-- Membership in the Berggren tree rooted at `(3,4,5)`. -/
inductive Reach : ℤ × ℤ × ℤ → Prop
  | root : Reach (3, 4, 5)
  | stepA {a b c : ℤ} : Reach (a, b, c) → Reach (bergA a b c)
  | stepB {a b c : ℤ} : Reach (a, b, c) → Reach (bergB a b c)
  | stepC {a b c : ℤ} : Reach (a, b, c) → Reach (bergC a b c)

theorem root_isPPT : IsPPT 3 4 5 :=
  ⟨by norm_num, by norm_num, by norm_num, by unfold IsPythag; norm_num, by decide, ⟨1, by ring⟩⟩

/-- Everything in the tree is a primitive triple with odd first leg. -/
theorem reach_isPPT {t : ℤ × ℤ × ℤ} (h : Reach t) : IsPPT t.1 t.2.1 t.2.2 := by
  induction h with
  | root => exact root_isPPT
  | stepA _ ih => exact bergA_isPPT ih
  | stepB _ ih => exact bergB_isPPT ih
  | stepC _ ih => exact bergC_isPPT ih

/-- The only Berggren triple with hypotenuse at most `5` is the root. -/
theorem small_isPPT {a b c : ℤ} (h : IsPPT a b c) (hc : c ≤ 5) : (a, b, c) = (3, 4, 5) := by
  obtain ⟨hac, hbc⟩ := h.legs_lt
  have hp := h.pyth
  unfold IsPythag at hp
  have ha := h.ha
  have hb := h.hb
  have hodd := h.odd
  rw [Int.odd_iff] at hodd
  have hc1 : 1 ≤ c := h.hc
  interval_cases c <;> interval_cases a <;> interval_cases b <;> simp_all

/-- **Descent theorem**: every primitive Pythagorean triple with odd first leg lies in the
Berggren tree.  The proof is by strong induction on the hypotenuse, using the parent map. -/
theorem isPPT_reach : ∀ (n : ℕ) (a b c : ℤ), c.toNat ≤ n → IsPPT a b c → Reach (a, b, c) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b c hn h
    by_cases hc : c ≤ 5
    · rw [small_isPPT h hc]; exact Reach.root
    · push_neg at hc
      have hpar := parent_isPPT h hc
      have hlt : (parent a b c).2.2 < c := parent_hyp_lt h
      have hposp : 0 < (parent a b c).2.2 := hpar.hc
      have hkey : (parent a b c).2.2.toNat < n := by
        have h1 : (parent a b c).2.2.toNat < c.toNat := by
          omega
        omega
      have hreach : Reach (parent a b c) :=
        ih _ hkey (parent a b c).1 (parent a b c).2.1 (parent a b c).2.2 (le_refl _) hpar
      rcases child_of_parent h hc with he | he | he
      · rw [he]; exact Reach.stepA hreach
      · rw [he]; exact Reach.stepB hreach
      · rw [he]; exact Reach.stepC hreach

/-- **Classification of the Berggren tree.**  The tree rooted at `(3,4,5)` and grown by the
three Berggren moves is exactly the set of primitive Pythagorean triples with positive
entries and odd first leg. -/
theorem reach_iff_isPPT (a b c : ℤ) : Reach (a, b, c) ↔ IsPPT a b c := by
  constructor
  · intro h; exact reach_isPPT h
  · intro h; exact isPPT_reach c.toNat a b c (le_refl _) h

/-- `IsPPT` is a decidable arithmetic condition. -/
instance decidableIsPPT (a b c : ℤ) : Decidable (IsPPT a b c) := by
  refine decidable_of_iff (0 < a ∧ 0 < b ∧ 0 < c ∧ a ^ 2 + b ^ 2 = c ^ 2 ∧
    Int.gcd a b = 1 ∧ a % 2 = 1) ?_
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2, h3, h4, h5, Int.odd_iff.mpr h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2, h3, h4, h5, Int.odd_iff.mp h6⟩

/-- **No Matiyasevich phenomenon for tree membership**: deciding whether a triple belongs to
the Berggren tree is an elementary arithmetic test (positivity, the Pythagorean equation,
coprimality and a parity check), so the membership problem is decidable. -/
instance decidableReach (t : ℤ × ℤ × ℤ) : Decidable (Reach t) := by
  obtain ⟨a, b, c⟩ := t
  exact decidable_of_iff (IsPPT a b c) (reach_iff_isPPT a b c).symm

end PythHydra


