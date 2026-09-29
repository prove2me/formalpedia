-- Prove2me | solution 1 for ECMParity.two_dvd_curveCard_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T12:52:02.255312+00:00
-- url     : https://prove2.me/submissions/68e7e82e-1138-46e5-9d8c-b09f6c8babdd

-- Sol generated from Algebra/ECMParityCore.lean
import Mathlib
import Definitions.Def_Algebra_ECMParityCore
import Theorems.Thm_ECMParity_affine_card_mod_two
/-
# ECM-PARITY, core: the parity of the point count of `y² = x³ + A x + B`

For an odd prime `p` and `A B : ZMod p` put

  `curveCard A B = 1 + #{(x,y) ∈ (ZMod p)² : y² = x³ + A x + B}`

(the `1` is the point at infinity of the projective Weierstrass model).

The main result of this file is the **parity dichotomy**

  `2 ∣ curveCard A B  ↔  the cubic x³ + A x + B has a root in ZMod p`

valid whenever the cubic is separable (`Δ = -4A³ - 27B² ≠ 0`).  Equivalently:
`#E` is odd exactly when Frobenius is a `3`-cycle on the roots of the cubic
(the cubic is irreducible over `𝔽_p`; see `ECMParityFrobenius.lean`).

The proof is elementary and self-contained:

* fibrewise counting: over each `x` the fibre `{y : y² = f x}` has odd
  cardinality iff `f x = 0`, hence `#affine ≡ #roots (mod 2)`;
* a separable cubic has `0`, `1` or `3` roots (never `2`), so `#roots` is odd
  iff `#roots ≠ 0`.

§0 collects the purely algebraic facts about a depressed cubic over an arbitrary
field (Vieta, the third root, the discriminant as a square of the root
difference product).  These are reused over the cubic extension `𝔽_{p³}` in
`ECMParityFrobenius.lean`.
-/

open ECMParity

open Finset

/-! ## 0. Depressed cubics over an arbitrary field -/




variable {F : Type*} [Field F] {A B a b x : F}

/-- Vieta for a depressed cubic with two known distinct roots: `A = -(a²+ab+b²)`. -/
theorem vieta_A (hab : a ≠ b) (ha : cubic A B a = 0) (hb : cubic A B b = 0) :
    A = -(a ^ 2 + a * b + b ^ 2) := by
  have hsub : (a - b) * (a ^ 2 + a * b + b ^ 2 + A) = 0 := by
    unfold cubic at ha hb; linear_combination ha - hb
  rcases mul_eq_zero.1 hsub with h | h
  · exact absurd (sub_eq_zero.1 h) hab
  · linear_combination h

/-- Vieta for a depressed cubic with two known distinct roots: `B = ab(a+b)`. -/
theorem vieta_B (hab : a ≠ b) (ha : cubic A B a = 0) (hb : cubic A B b = 0) :
    B = a * b * (a + b) := by
  have hA := vieta_A hab ha hb
  unfold cubic at ha; rw [hA] at ha; linear_combination ha

/-- The third root of a depressed cubic with two known distinct roots is `-(a+b)`
(the roots sum to zero). -/
theorem cubic_neg_add (hab : a ≠ b) (ha : cubic A B a = 0) (hb : cubic A B b = 0) :
    cubic A B (-(a + b)) = 0 := by
  rw [cubic, vieta_A hab ha hb, vieta_B hab ha hb]; ring

/-- With two distinct roots known, *every* root is one of `a`, `b`, `-(a+b)`. -/
theorem root_cases (hab : a ≠ b) (ha : cubic A B a = 0) (hb : cubic A B b = 0)
    (hx : cubic A B x = 0) : x = a ∨ x = b ∨ x = -(a + b) := by
  have hfac : (x - a) * (x - b) * (x - (-(a + b))) = 0 := by
    unfold cubic at hx
    rw [vieta_A hab ha hb, vieta_B hab ha hb] at hx
    linear_combination hx
  rcases mul_eq_zero.1 hfac with h | h
  · rcases mul_eq_zero.1 h with h' | h'
    · exact Or.inl (sub_eq_zero.1 h')
    · exact Or.inr (Or.inl (sub_eq_zero.1 h'))
  · exact Or.inr (Or.inr (sub_eq_zero.1 h))


/-- For a separable cubic the third root differs from the first. -/
theorem third_root_ne_left (hab : a ≠ b) (ha : cubic A B a = 0) (hb : cubic A B b = 0)
    (hd : disc A B ≠ 0) : -(a + b) ≠ a := by
  intro h
  apply hd
  have hb2 : b = -2 * a := by linear_combination -h
  rw [disc, vieta_A hab ha hb, vieta_B hab ha hb, hb2]; ring

/-- For a separable cubic the third root differs from the second. -/
theorem third_root_ne_right (hab : a ≠ b) (ha : cubic A B a = 0) (hb : cubic A B b = 0)
    (hd : disc A B ≠ 0) : -(a + b) ≠ b := by
  intro h
  apply hd
  have ha2 : a = -2 * b := by linear_combination -h
  rw [disc, vieta_A hab ha hb, vieta_B hab ha hb, ha2]; ring


/-! ## 1. Fibrewise counting over `𝔽_p` -/

variable {p : ℕ} [Fact p.Prime]







/-- The projective point count is even iff the number of roots of the cubic is odd. -/
theorem curveCard_even_iff_odd_rootSet (hp : p ≠ 2) (A B : ZMod p) :
    2 ∣ curveCard A B ↔ Odd (rootSet A B).card := by
  have h := affine_card_mod_two hp A B
  have key : (((affinePoints A B).card) % 2) = ((rootSet A B).card % 2) := by
    have := (ZMod.natCast_eq_natCast_iff' _ _ 2).1 h
    simpa using this
  unfold curveCard
  rw [Nat.odd_iff]
  omega

/-! ## 2. A separable cubic has `0`, `1` or `3` roots -/

/-- If a depressed cubic has two distinct roots `a ≠ b`, its root set is exactly
`{a, b, -(a+b)}`. -/
theorem rootSet_eq_of_two_roots {A B a b : ZMod p} (hab : a ≠ b)
    (ha : cubic A B a = 0) (hb : cubic A B b = 0) :
    rootSet A B = {a, b, -(a + b)} := by
  ext x
  simp only [rootSet, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · exact fun hx => root_cases hab ha hb hx
  · rintro (rfl | rfl | rfl)
    · exact ha
    · exact hb
    · exact cubic_neg_add hab ha hb

/-- With a nonzero discriminant, two distinct roots force a third one:
the root set has exactly three elements. -/
theorem rootSet_card_eq_three {A B a b : ZMod p} (hab : a ≠ b)
    (ha : cubic A B a = 0) (hb : cubic A B b = 0) (hd : disc A B ≠ 0) :
    (rootSet A B).card = 3 := by
  have hca : -(a + b) ≠ a := third_root_ne_left hab ha hb hd
  have hcb : -(a + b) ≠ b := third_root_ne_right hab ha hb hd
  rw [rootSet_eq_of_two_roots hab ha hb]
  rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hab, fun h => hca (by linear_combination -h)⟩),
    Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton]
      exact fun h => hcb (by linear_combination -h)), Finset.card_singleton]

/-- A separable depressed cubic over `𝔽_p` has `0`, `1` or `3` roots. -/
theorem rootSet_card_cases (A B : ZMod p) (hd : disc A B ≠ 0) :
    (rootSet A B).card = 0 ∨ (rootSet A B).card = 1 ∨ (rootSet A B).card = 3 := by
  rcases Nat.lt_or_ge (rootSet A B).card 2 with h | h
  · interval_cases hc : (rootSet A B).card
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h
    simp only [rootSet, mem_filter] at ha hb
    exact Or.inr (Or.inr (rootSet_card_eq_three hab ha.2 hb.2 hd))

/-! ## 3. The parity dichotomy -/




open ECMParity in
theorem solution(hp : p ≠ 2) (A B : ZMod p) (hd : disc A B ≠ 0) :
    2 ∣ curveCard A B ↔ ∃ x : ZMod p, cubic A B x = 0 := by
  rw [curveCard_even_iff_odd_rootSet hp]
  constructor
  · intro hodd
    have hne : (rootSet A B).Nonempty := by
      rw [← Finset.card_pos]
      rcases hodd with ⟨k, hk⟩; omega
    obtain ⟨x, hx⟩ := hne
    exact ⟨x, by simpa [rootSet] using hx⟩
  · intro ⟨x, hx⟩
    have hne : (rootSet A B).card ≠ 0 := by
      intro h
      have hx' : x ∈ rootSet A B := by simp [rootSet, hx]
      rw [Finset.card_eq_zero] at h
      rw [h] at hx'
      simp at hx'
    rcases rootSet_card_cases A B hd with h | h | h
    · exact absurd h hne
    · rw [h]; exact ⟨0, rfl⟩
    · rw [h]; exact ⟨1, rfl⟩
