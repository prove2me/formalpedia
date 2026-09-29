-- Prove2me | solution 1 for Price2Adic.eval_injective
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T14:50:45.484362+00:00
-- url     : https://prove2.me/submissions/6b5b0ebd-5b63-498b-8986-85f837870b13

import Definitions.Def_Cryptography_Price2Adic_Tree

open Price2Adic

open Price2Adic in
/-- **Uniqueness for the Price tree**: distinct Price words address distinct nodes. -/
theorem solution : Function.Injective eval := by
  -- `eval` of a word with one letter appended is one `step` on `eval` of the word.
  have heval : ∀ (w : PriceWord) (l : PriceLetter), eval (w ++ [l]) = step l (eval w) := by
    intro w l
    simp [eval]
  -- An odd divisor of `2 * n` divides `n`.
  have hodd2 : ∀ d n : ℕ, d % 2 = 1 → d ∣ 2 * n → d ∣ n := by
    intro d n hodd h
    have hnd : ¬ (2 ∣ d) := by omega
    have hc : Nat.Coprime 2 d := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hnd
    exact (Nat.Coprime.symm hc).dvd_of_dvd_mul_left h
  -- A divisor of an odd number is odd.
  have hdodd : ∀ d x : ℕ, d ∣ x → x % 2 = 1 → d % 2 = 1 := by
    intro d x hdx hx
    by_contra hcon
    have h2d : (2 : ℕ) ∣ d := by omega
    have h2x : (2 : ℕ) ∣ x := h2d.trans hdx
    omega
  -- Coprimality of a parent pair, from coprimality of `m` and `n`.
  have hcop : ∀ a b m n : ℕ, Nat.gcd m n = 1 →
      Nat.gcd a b ∣ m → Nat.gcd a b ∣ n → Nat.gcd a b = 1 := by
    intro a b m n hg h1 h2
    have h3 := Nat.dvd_gcd h1 h2
    rw [hg] at h3
    exact Nat.dvd_one.mp h3
  have hvroot : Valid root := by decide
  -- Each move preserves validity.
  have hvstep : ∀ (l : PriceLetter) (q : ℕ × ℕ), Valid q → Valid (step l q) := by
    rintro l ⟨m, n⟩ hq
    obtain ⟨hn, hlt, hg, hpar⟩ := hq
    cases l
    · -- A : (m + n, 2n)
      simp only [step]
      refine ⟨by omega, by omega, ?_, by omega⟩
      have k1 : Nat.gcd (m + n) (2 * n) ∣ m + n := Nat.gcd_dvd_left _ _
      have k2 : Nat.gcd (m + n) (2 * n) ∣ 2 * n := Nat.gcd_dvd_right _ _
      have ho : Nat.gcd (m + n) (2 * n) % 2 = 1 := hdodd _ _ k1 hpar
      have kn : Nat.gcd (m + n) (2 * n) ∣ n := hodd2 _ _ ho k2
      have km : Nat.gcd (m + n) (2 * n) ∣ m := by
        have h3 := Nat.dvd_sub k1 kn
        have e : m + n - n = m := by omega
        rwa [e] at h3
      exact hcop _ _ m n hg km kn
    · -- B : (2m, m - n)
      simp only [step]
      refine ⟨by omega, by omega, ?_, by omega⟩
      have k1 : Nat.gcd (2 * m) (m - n) ∣ 2 * m := Nat.gcd_dvd_left _ _
      have k2 : Nat.gcd (2 * m) (m - n) ∣ m - n := Nat.gcd_dvd_right _ _
      have ho : Nat.gcd (2 * m) (m - n) % 2 = 1 := hdodd _ _ k2 (by omega)
      have km : Nat.gcd (2 * m) (m - n) ∣ m := hodd2 _ _ ho k1
      have kn : Nat.gcd (2 * m) (m - n) ∣ n := by
        have h3 := Nat.dvd_sub km k2
        have e : m - (m - n) = n := by omega
        rwa [e] at h3
      exact hcop _ _ m n hg km kn
    · -- C : (2m, m + n)
      simp only [step]
      refine ⟨by omega, by omega, ?_, by omega⟩
      have k1 : Nat.gcd (2 * m) (m + n) ∣ 2 * m := Nat.gcd_dvd_left _ _
      have k2 : Nat.gcd (2 * m) (m + n) ∣ m + n := Nat.gcd_dvd_right _ _
      have ho : Nat.gcd (2 * m) (m + n) % 2 = 1 := hdodd _ _ k2 hpar
      have km : Nat.gcd (2 * m) (m + n) ∣ m := hodd2 _ _ ho k1
      have kn : Nat.gcd (2 * m) (m + n) ∣ n := by
        have h3 := Nat.dvd_sub k2 km
        have e : m + n - m = n := by omega
        rwa [e] at h3
      exact hcop _ _ m n hg km kn
  -- The recorded letter is the letter of the move.
  have hlet : ∀ (l : PriceLetter) (q : ℕ × ℕ), Valid q → letterOf (step l q) = l := by
    rintro l ⟨m, n⟩ hq
    obtain ⟨hn, hlt, hg, hpar⟩ := hq
    cases l
    · simp only [step, letterOf]
      rw [if_pos (by omega : (2 * n) % 2 = 0)]
    · simp only [step, letterOf]
      rw [if_neg (by omega : ¬ ((m - n) % 2 = 0)), if_pos (by omega : 2 * (m - n) < 2 * m)]
    · simp only [step, letterOf]
      rw [if_neg (by omega : ¬ ((m + n) % 2 = 0)), if_neg (by omega : ¬ (2 * (m + n) < 2 * m))]
  -- `parent` undoes each move.
  have hpar2 : ∀ (l : PriceLetter) (q : ℕ × ℕ), Valid q → parent (step l q) = q := by
    rintro l ⟨m, n⟩ hq
    obtain ⟨hn, hlt, hg, hpar⟩ := hq
    cases l
    · simp only [step, parent]
      rw [if_pos (by omega : (2 * n) % 2 = 0)]
      simp only [Prod.mk.injEq]; omega
    · simp only [step, parent]
      rw [if_neg (by omega : ¬ ((m - n) % 2 = 0)), if_pos (by omega : 2 * (m - n) < 2 * m)]
      simp only [Prod.mk.injEq]; omega
    · simp only [step, parent]
      rw [if_neg (by omega : ¬ ((m + n) % 2 = 0)), if_neg (by omega : ¬ (2 * (m + n) < 2 * m))]
      simp only [Prod.mk.injEq]; omega
  -- No move lands back on the root.
  have hnotroot : ∀ (l : PriceLetter) (q : ℕ × ℕ), Valid q → step l q ≠ root := by
    rintro l ⟨m, n⟩ hq
    obtain ⟨hn, hlt, hg, hpar⟩ := hq
    cases l <;>
      simp only [step, root, ne_eq, Prod.mk.injEq, not_and] <;>
      intro h <;> omega
  -- Every evaluated word is a valid node.
  have hveval : ∀ w : PriceWord, Valid (eval w) := by
    intro w
    induction w using List.reverseRecOn
    · exact hvroot
    · rename_i w l ih
      rw [heval]
      exact hvstep l (eval w) ih
  -- The address of an evaluated word is that word: `address` is a left inverse of `eval`.
  have haddr : ∀ w : PriceWord, address (eval w) = w := by
    intro w
    induction w using List.reverseRecOn
    · have he : eval ([] : PriceWord) = root := rfl
      rw [he, address]
      exact dif_neg (by rintro ⟨-, h2⟩; exact h2 rfl)
    · rename_i w l ih
      have hv : Valid (eval w) := hveval w
      have hunfold : address (step l (eval w))
          = address (parent (step l (eval w))) ++ [letterOf (step l (eval w))] := by
        rw [address]
        exact dif_pos ⟨hvstep l (eval w) hv, hnotroot l (eval w) hv⟩
      rw [heval, hunfold, hpar2 l (eval w) hv, hlet l (eval w) hv, ih]
  -- Injectivity follows: apply the left inverse to both sides.
  intro w1 w2 h
  have h1 := haddr w1
  rw [h, haddr w2] at h1
  exact h1.symm
