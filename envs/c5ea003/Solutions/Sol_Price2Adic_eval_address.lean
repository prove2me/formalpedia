-- Prove2me | solution 1 for Price2Adic.eval_address
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T14:40:59.780299+00:00
-- url     : https://prove2.me/submissions/a291be25-d456-4d61-9848-64b56c881a65

import Definitions.Def_Cryptography_Price2Adic_Tree

open Price2Adic

open Price2Adic in
/-- **Completeness of the Price tree**: every valid Euclid parameter pair is
reached by evaluating its own address. -/
theorem solution (p : ℕ × ℕ) (hp : Valid p) : eval (address p) = p := by
  -- `eval` of a word with one letter appended is one `step` on `eval` of the word.
  have heval : ∀ (w : PriceWord) (l : PriceLetter), eval (w ++ [l]) = step l (eval w) := by
    intro w l
    simp [eval]
  -- The parent of a valid non-root node is valid.
  have hvalid : ∀ q : ℕ × ℕ, Valid q → q ≠ root → Valid (parent q) := by
    rintro ⟨m, n⟩ hq hroot
    obtain ⟨hn, hlt, hg, hpar⟩ := hq
    simp only [parent]
    split_ifs with h1 h2
    · -- A : n even, parent = (m - n/2, n/2)
      refine ⟨by omega, by omega, ?_, by omega⟩
      have k1 := Nat.gcd_dvd_left (m - n / 2) (n / 2)
      have k2 := Nat.gcd_dvd_right (m - n / 2) (n / 2)
      have hm : Nat.gcd (m - n / 2) (n / 2) ∣ m := by
        have h3 := dvd_add k1 k2
        have e : (m - n / 2) + n / 2 = m := by omega
        rwa [e] at h3
      have hn2 : Nat.gcd (m - n / 2) (n / 2) ∣ n := by
        have h3 := dvd_add k2 k2
        have e : n / 2 + n / 2 = n := by omega
        rwa [e] at h3
      have hd := Nat.dvd_gcd hm hn2
      rw [hg] at hd
      exact Nat.dvd_one.mp hd
    · -- B : n odd, 2n < m, parent = (m/2, m/2 - n)
      refine ⟨by omega, by omega, ?_, by omega⟩
      have k1 := Nat.gcd_dvd_left (m / 2) (m / 2 - n)
      have k2 := Nat.gcd_dvd_right (m / 2) (m / 2 - n)
      have hm : Nat.gcd (m / 2) (m / 2 - n) ∣ m := by
        have h3 := dvd_add k1 k1
        have e : m / 2 + m / 2 = m := by omega
        rwa [e] at h3
      have hn2 : Nat.gcd (m / 2) (m / 2 - n) ∣ n := by
        have h3 : Nat.gcd (m / 2) (m / 2 - n) ∣ m / 2 - (m / 2 - n) :=
          Nat.dvd_sub k1 k2
        have e : m / 2 - (m / 2 - n) = n := by omega
        rwa [e] at h3
      have hd := Nat.dvd_gcd hm hn2
      rw [hg] at hd
      exact Nat.dvd_one.mp hd
    · -- C : n odd, m ≤ 2n, parent = (m/2, n - m/2).  Strictness is where `hroot` is used.
      have hstrict : m / 2 < n := by
        rcases Nat.lt_or_ge (m / 2) n with h | h
        · exact h
        · exfalso
          have hm2 : m = 2 * n := by omega
          have hdvd : n ∣ Nat.gcd m n := Nat.dvd_gcd ⟨2, by omega⟩ dvd_rfl
          rw [hg] at hdvd
          have hn1 : n = 1 := Nat.dvd_one.mp hdvd
          apply hroot
          simp only [root, Prod.mk.injEq]
          omega
      refine ⟨by omega, by omega, ?_, by omega⟩
      have k1 := Nat.gcd_dvd_left (m / 2) (n - m / 2)
      have k2 := Nat.gcd_dvd_right (m / 2) (n - m / 2)
      have hm : Nat.gcd (m / 2) (n - m / 2) ∣ m := by
        have h3 := dvd_add k1 k1
        have e : m / 2 + m / 2 = m := by omega
        rwa [e] at h3
      have hn2 : Nat.gcd (m / 2) (n - m / 2) ∣ n := by
        have h3 := dvd_add k2 k1
        have e : (n - m / 2) + m / 2 = n := by omega
        rwa [e] at h3
      have hd := Nat.dvd_gcd hm hn2
      rw [hg] at hd
      exact Nat.dvd_one.mp hd
  -- One step back up: the last letter recovers the node from its parent.
  have hstep : ∀ q : ℕ × ℕ, Valid q → q ≠ root → step (letterOf q) (parent q) = q := by
    rintro ⟨m, n⟩ hq _
    obtain ⟨hn, hlt, hg, hpar⟩ := hq
    simp only [letterOf, parent]
    split_ifs with h1 h2 <;> simp only [step, Prod.mk.injEq] <;> omega
  -- Induct on a bound for the measure `q.1 + q.2` that `address` recurses on.
  have main : ∀ N (q : ℕ × ℕ), q.1 + q.2 ≤ N → Valid q → eval (address q) = q := by
    intro N
    induction N with
    | zero =>
        rintro ⟨m, n⟩ hle hq
        obtain ⟨hn, hlt, hg, hpar⟩ := hq
        have h0 : m + n ≤ 0 := hle
        omega
    | succ N ih =>
        intro q hle hq
        rw [address]
        split_ifs with h
        · have hb : (parent q).1 + (parent q).2 ≤ N := by
            have := parent_sum_lt q hq h.2
            omega
          rw [heval, ih (parent q) hb (hvalid q hq h.2)]
          exact hstep q hq h.2
        · have hr : q = root := by
            by_contra hc
            exact h ⟨hq, hc⟩
          rw [hr]
          rfl
  exact main (p.1 + p.2) p le_rfl hp
