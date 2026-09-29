-- Prove2me | solution 1 for Cryptography.BerggrenModular.prime_not_dvd_leg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:17:11.146479+00:00
-- url     : https://prove2.me/submissions/728dbc24-61f8-4216-aa3c-55a6bd786b3a

-- Sol generated from Cryptography/BerggrenModular/BlumImmunity.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_BlumImmunity
import Definitions.Def_Cryptography_BerggrenModular_NullCone

/-!
# The ambient null: the Berggren hypotenuse stream cannot see primes `≡ 3 (mod 4)`

The modular-dynamics experiment (exp 555) reports that the mod-`N` Berggren orbit
*under-samples factor-revealing residues* relative to random Pythagorean points.
This file isolates a hard, exact structural reason for a large part of that
deficit, and proves it.

Every node of the Berggren tree is a **primitive** Pythagorean triple
(`Cryptography.BerggrenModular.NullCone.Prim_applyWord`).  A classical fact —
proved here from scratch — is that the hypotenuse of a primitive Pythagorean
triple has *only* prime divisors `≡ 1 (mod 4)`.  Consequently a "dive" that
inspects `gcd(c, N)` along the tree

* can never expose a prime factor `p ≡ 3 (mod 4)` of `N`, and
* is **completely blind** on Blum integers `N = pq`, `p ≡ q ≡ 3 (mod 4)` — the
  moduli used in Rabin/Blum–Blum–Shub and a positive-density share of RSA-like
  moduli — no matter how deep the traversal goes.

## Main results

* `hyp_not_even` — the hypotenuse of a primitive Pythagorean triple is odd.
* `prime_not_dvd_leg` — a prime dividing the hypotenuse divides neither leg.
* `prime_dvd_hyp_mod_four` — **every prime divisor of the hypotenuse of a
  primitive Pythagorean triple is `≡ 1 (mod 4)`.**
* `berggren_hyp_prime_divisors_one_mod_four` — the same for every node of the
  Berggren tree.
* `berggren_gcd_eq_one_of_all_prime_factors_three_mod_four` — the hypotenuse of
  every node is coprime to any modulus all of whose prime factors are `≡ 3 (4)`.
* `berggren_dive_blind_on_blum` — **Blum-integer immunity**: for `N = p*q` with
  `p ≡ q ≡ 3 (mod 4)` the hypotenuse dive reveals nothing at any depth.
* `berggren_dive_undersamples` — for `N = p*q` with `p ≡ 3 (mod 4)` the only
  factor the dive can ever return is `q`: half of the factor-revealing residues
  are structurally unreachable.
-/

open Cryptography
open BerggrenModular

/-! ## Primitive Pythagorean triples: the hypotenuse is `1 (mod 4)`-smooth -/

/-- The hypotenuse of a primitive Pythagorean triple is odd. -/
theorem hyp_not_even {a b c : ℤ} (hpy : a ^ 2 + b ^ 2 = c ^ 2)
    (hprim : ∀ d : ℤ, d ∣ a → d ∣ b → d ∣ c → IsUnit d) : ¬ ((2 : ℤ) ∣ c) := by
  rintro ⟨k, rfl⟩
  rcases Int.even_or_odd a with ⟨s, rfl⟩ | ⟨s, rfl⟩ <;>
    rcases Int.even_or_odd b with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · have h := hprim 2 ⟨s, by ring⟩ ⟨t, by ring⟩ ⟨k, rfl⟩
    rw [Int.isUnit_iff] at h; omega
  · have h4 : (4 : ℤ) ∣ 1 := ⟨k ^ 2 - s ^ 2 - t ^ 2 - t, by linarith [hpy]⟩
    norm_num at h4
  · have h4 : (4 : ℤ) ∣ 1 := ⟨k ^ 2 - s ^ 2 - s - t ^ 2, by linarith [hpy]⟩
    norm_num at h4
  · have h4 : (4 : ℤ) ∣ 2 := ⟨k ^ 2 - s ^ 2 - s - t ^ 2 - t, by linarith [hpy]⟩
    norm_num at h4

/-- A prime dividing the hypotenuse of a primitive triple divides neither leg. -/
theorem prime_not_dvd_leg {a b c : ℤ} (hpy : a ^ 2 + b ^ 2 = c ^ 2)
    (hprim : ∀ d : ℤ, d ∣ a → d ∣ b → d ∣ c → IsUnit d)
    {p : ℕ} (hp : p.Prime) (hd : (p : ℤ) ∣ c) : ¬ ((p : ℤ) ∣ a) := by
  intro hda
  have hdb : (p : ℤ) ∣ b := by
    have hb2 : (p : ℤ) ∣ b ^ 2 := by
      have hbe : b ^ 2 = c ^ 2 - a ^ 2 := by linarith
      rw [hbe]
      exact dvd_sub (dvd_pow hd two_ne_zero) (dvd_pow hda two_ne_zero)
    exact Int.Prime.dvd_pow' (by exact_mod_cast hp) hb2
  have hu := hprim p hda hdb hd
  rw [Int.isUnit_iff] at hu
  have := hp.two_le
  omega

/-- Symmetric version: the prime divides neither leg. -/
theorem prime_not_dvd_leg' {a b c : ℤ} (hpy : a ^ 2 + b ^ 2 = c ^ 2)
    (hprim : ∀ d : ℤ, d ∣ a → d ∣ b → d ∣ c → IsUnit d)
    {p : ℕ} (hp : p.Prime) (hd : (p : ℤ) ∣ c) : ¬ ((p : ℤ) ∣ b) := by
  refine prime_not_dvd_leg (a := b) (b := a) (by linarith) ?_ hp hd
  intro d h1 h2 h3
  exact hprim d h2 h1 h3

/-- **The hypotenuse of a primitive Pythagorean triple is `1 (mod 4)`-smooth.**
Every prime divisor of `c` is congruent to `1` modulo `4`.  The proof: such a
prime is odd (else `2 ∣ c` contradicts primitivity mod `4`), it divides neither
leg, and `a² ≡ -b² (mod p)` with `b` invertible makes `-1` a square mod `p`. -/
theorem prime_dvd_hyp_mod_four {a b c : ℤ} (hpy : a ^ 2 + b ^ 2 = c ^ 2)
    (hprim : ∀ d : ℤ, d ∣ a → d ∣ b → d ∣ c → IsUnit d)
    {p : ℕ} (hp : p.Prime) (hd : (p : ℤ) ∣ c) : p % 4 = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2 : p ≠ 2 := by
    rintro rfl
    exact hyp_not_even hpy hprim (by exact_mod_cast hd)
  have hnb : ¬ ((p : ℤ) ∣ b) := prime_not_dvd_leg' hpy hprim hp hd
  have hc0 : ((c : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd c p).2 hd
  have hA : ((a : ZMod p)) ^ 2 + ((b : ZMod p)) ^ 2 = 0 := by
    have h := congrArg (fun z : ℤ => ((z : ZMod p))) hpy
    push_cast at h
    rw [h, hc0]; ring
  have hbne : ((b : ZMod p)) ≠ 0 := fun h => hnb ((ZMod.intCast_zmod_eq_zero_iff_dvd b p).1 h)
  have hsq : IsSquare (-1 : ZMod p) := by
    refine ⟨(a : ZMod p) * ((b : ZMod p))⁻¹, ?_⟩
    field_simp
    linear_combination -hA
  have h3 := (ZMod.exists_sq_eq_neg_one_iff (p := p)).1 hsq
  have hodd : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two h2)
  omega




/-! ## Transport to the Berggren tree -/

/-- Every Berggren move is an isometry of the Lorentz form. -/
theorem lorentz_applyMove (i : Move) (v : Tri) : lorentz (applyMove i v) = lorentz v := by
  cases i <;> simp only [lorentz, applyMove] <;> ring

theorem valid_leg_lt_hyp₁ {v : Tri} (h : Valid v) : v.1 < v.2.2 := by
  obtain ⟨ha, hb, hc, hp⟩ := h; nlinarith

theorem valid_leg_lt_hyp₂ {v : Tri} (h : Valid v) : v.2.1 < v.2.2 := by
  obtain ⟨ha, hb, hc, hp⟩ := h; nlinarith

theorem applyMove_valid {i : Move} {v : Tri} (h : Valid v) : Valid (applyMove i v) := by
  have h1 := valid_leg_lt_hyp₁ h
  have h2 := valid_leg_lt_hyp₂ h
  obtain ⟨ha, hb, hc, hp⟩ := h
  cases i <;>
    refine ⟨by simp only [applyMove]; linarith, by simp only [applyMove]; linarith,
      by simp only [applyMove]; linarith, ?_⟩ <;>
    simp only [applyMove] <;> linear_combination hp

theorem root_valid : Valid root := by
  refine ⟨by norm_num [root], by norm_num [root], by norm_num [root], by norm_num [root]⟩

@[simp] theorem applyWord_cons (i : Move) (w : List Move) (v : Tri) :
    applyWord (i :: w) v = applyMove i (applyWord w v) := rfl

theorem applyWord_valid (w : List Move) {v : Tri} (h : Valid v) : Valid (applyWord w v) := by
  induction w with
  | nil => exact h
  | cons i rest ih => exact applyMove_valid ih

/-- A triple is primitive when its three entries have no common non-unit divisor. -/
theorem Prim_root : Prim root := by
  intro d h1 h2 _
  have : d ∣ (1 : ℤ) := by
    have := dvd_sub h2 h1
    simpa [root] using this
  exact isUnit_of_dvd_one this

theorem Prim_applyMove {i : Move} {v : Tri} (h : Prim v) : Prim (applyMove i v) := by
  intro d h1 h2 h3
  cases i
  · simp only [applyMove] at h1 h2 h3
    obtain ⟨x, hx⟩ := h1; obtain ⟨y, hy⟩ := h2; obtain ⟨z, hz⟩ := h3
    exact h d ⟨x + 2 * y - 2 * z, by linear_combination hx + 2 * hy - 2 * hz⟩
      ⟨-2 * x - y + 2 * z, by linear_combination -2 * hx - hy + 2 * hz⟩
      ⟨-2 * x - 2 * y + 3 * z, by linear_combination -2 * hx - 2 * hy + 3 * hz⟩
  · simp only [applyMove] at h1 h2 h3
    obtain ⟨x, hx⟩ := h1; obtain ⟨y, hy⟩ := h2; obtain ⟨z, hz⟩ := h3
    exact h d ⟨x + 2 * y - 2 * z, by linear_combination hx + 2 * hy - 2 * hz⟩
      ⟨2 * x + y - 2 * z, by linear_combination 2 * hx + hy - 2 * hz⟩
      ⟨-2 * x - 2 * y + 3 * z, by linear_combination -2 * hx - 2 * hy + 3 * hz⟩
  · simp only [applyMove] at h1 h2 h3
    obtain ⟨x, hx⟩ := h1; obtain ⟨y, hy⟩ := h2; obtain ⟨z, hz⟩ := h3
    exact h d ⟨-x - 2 * y + 2 * z, by linear_combination -hx - 2 * hy + 2 * hz⟩
      ⟨2 * x + y - 2 * z, by linear_combination 2 * hx + hy - 2 * hz⟩
      ⟨-2 * x - 2 * y + 3 * z, by linear_combination -2 * hx - 2 * hy + 3 * hz⟩

theorem Prim_applyWord (u : List Move) : Prim (applyWord u root) := by
  induction u with
  | nil => exact Prim_root
  | cons i rest ih => exact Prim_applyMove ih

theorem lorentz_applyWord (u : List Move) : lorentz (applyWord u root) = 0 := by
  induction u with
  | nil => rfl
  | cons i rest ih => rw [applyWord_cons, lorentz_applyMove]; exact ih

/-- The Pythagorean identity at every node of the Berggren tree. -/
theorem pyth_applyWord (u : List Move) :
    (applyWord u root).1 ^ 2 + (applyWord u root).2.1 ^ 2 = (applyWord u root).2.2 ^ 2 := by
  have h := lorentz_applyWord u
  simp only [lorentz] at h
  linarith

/-- **Every prime divisor of a Berggren hypotenuse is `≡ 1 (mod 4)`.** -/
theorem berggren_hyp_prime_divisors_one_mod_four (u : List Move) {p : ℕ} (hp : p.Prime)
    (hd : (p : ℤ) ∣ (applyWord u root).2.2) : p % 4 = 1 :=
  prime_dvd_hyp_mod_four (pyth_applyWord u) (Prim_applyWord u) hp hd

theorem coe_hypNat (u : List Move) : ((hypNat u : ℕ) : ℤ) = (applyWord u root).2.2 := by
  have h := (applyWord_valid u root_valid).2.2.1
  simp [hypNat, Int.toNat_of_nonneg h.le]




/-! ## Blindness of the hypotenuse dive -/

theorem hypNat_prime_factors_one_mod_four (u : List Move) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ hypNat u) : p % 4 = 1 := by
  refine berggren_hyp_prime_divisors_one_mod_four u hp ?_
  rw [← coe_hypNat u]
  exact_mod_cast hd

/-- If every prime factor of `N` is `≡ 3 (mod 4)` then the hypotenuse of every
Berggren node is coprime to `N`: the `gcd` dive returns `1` forever. -/
theorem berggren_gcd_eq_one_of_all_prime_factors_three_mod_four (u : List Move) {N : ℕ}
    (hN : ∀ r : ℕ, r.Prime → r ∣ N → r % 4 = 3) : Nat.gcd (hypNat u) N = 1 := by
  by_contra hne
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hne
  have h1 : r % 4 = 1 := hypNat_prime_factors_one_mod_four u hr (hrd.trans (Nat.gcd_dvd_left _ _))
  have h3 : r % 4 = 3 := hN r hr (hrd.trans (Nat.gcd_dvd_right _ _))
  omega

/-- **Blum-integer immunity of the Berggren hypotenuse dive.**  For a Blum
modulus the dive's `gcd` is identically `1`, at every node, at every depth: the
modular Berggren descent conveys *zero* information about the factorisation. -/
theorem berggren_dive_blind_on_blum {N : ℕ} (hN : IsBlum N) (u : List Move) :
    Nat.gcd (hypNat u) N = 1 := by
  obtain ⟨p, q, hp, hq, hp3, hq3, rfl⟩ := hN
  refine berggren_gcd_eq_one_of_all_prime_factors_three_mod_four u ?_
  intro r hr hrd
  rcases (Nat.Prime.dvd_mul hr).1 hrd with h | h
  · rw [(Nat.prime_dvd_prime_iff_eq hr hp).1 h]; exact hp3
  · rw [(Nat.prime_dvd_prime_iff_eq hr hq).1 h]; exact hq3

/-- Non-vacuity of `IsBlum`: `21 = 3·7` is a Blum integer, and the dive is blind
on it at every depth. -/
example : IsBlum 21 := ⟨3, 7, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

example (u : List Move) : Nat.gcd (hypNat u) 21 = 1 :=
  berggren_dive_blind_on_blum
    ⟨3, 7, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩ u

/-- Sharpness: the blindness is caused by the residue `3 (mod 4)`, not by the
search.  For `N = 65 = 5·13` the dive already splits `N` at depth two: the node
`B₃B₂` has hypotenuse `85` and `gcd(85, 65) = 5`. -/
example : hypNat [Move.m3, Move.m2] = 85 := by decide

example : Nat.gcd (hypNat [Move.m3, Move.m2]) 65 = 5 := by decide

/-- Sharpness in the other direction: the `1 (mod 4)` law is a property of the
*hypotenuse* only.  The legs are unconstrained — the node `B₁(3,4,5) = (5,12,13)`
has a leg divisible by `3` — so a leg-based dive is not structurally blind on Blum
moduli.  It is still trial-division-class, by the counting theorems in
`Cryptography.BerggrenModular.TrialDivisionEquivalence`. -/
example : (3 : ℤ) ∣ (applyWord [Move.m1] root).2.1 := by decide




open Cryptography in
theorem solution{a b c : ℤ} (hpy : a ^ 2 + b ^ 2 = c ^ 2)
    (hprim : ∀ d : ℤ, d ∣ a → d ∣ b → d ∣ c → IsUnit d)
    {p : ℕ} (hp : p.Prime) (hd : (p : ℤ) ∣ c) : ¬ ((p : ℤ) ∣ a) := by
  intro hda
  have hdb : (p : ℤ) ∣ b := by
    have hb2 : (p : ℤ) ∣ b ^ 2 := by
      have hbe : b ^ 2 = c ^ 2 - a ^ 2 := by linarith
      rw [hbe]
      exact dvd_sub (dvd_pow hd two_ne_zero) (dvd_pow hda two_ne_zero)
    exact Int.Prime.dvd_pow' (by exact_mod_cast hp) hb2
  have hu := hprim p hda hdb hd
  rw [Int.isUnit_iff] at hu
  have := hp.two_le
  omega
