-- Prove2me | solution 2 for GCDMoment.pairMoment_injective_of_three_le_unconditional
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T21:57:30.689556+00:00
-- url     : https://prove2.me/submissions/cf25cefe-be36-4b8a-bccc-e4713debb7dd

import Mathlib
import Definitions.Def_Novelty_GCDMomentHigherInversion
import Definitions.Def_Novelty_GCDMomentPairInversion

set_option maxHeartbeats 1600000 in
open GCDMoment in
theorem solution {a b c d : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hc : 2 ≤ c)
    (hcd : c ≤ d) (hprod : a * b = c * d) (m : ℕ)
    (hm : pairMoment (m + 3) (a : ℤ) (b : ℤ) = pairMoment (m + 3) (c : ℤ) (d : ℤ)) :
    a = c ∧ b = d := by
  classical
  -- purely algebraic core: the bracket is positive under a linear size condition
  have core : ∀ (N ga de al g A B p q : ℤ), 1 ≤ A → 1 ≤ B → 1 ≤ p → 1 ≤ q →
      0 ≤ ga → 0 ≤ de → 0 ≤ al → 0 ≤ g → 2 * p ≤ A → 2 * q ≤ B →
      N = g * al * ga * de →
      4 * (ga * de) + 2 * (g * ga) + 2 * (al * de) + g * al + 4 < 4 * N →
      0 < N * A * B - (ga * A + al * p) * (de * B + g * q) - 1 := by
    intro N ga de al g A B p q hA1 hB1 hp1 hq1 hga0 hde0 hal0 hg0 hpA hqB hN hsize
    have hA0 : (0 : ℤ) ≤ A := by linarith
    have hB0 : (0 : ℤ) ≤ B := by linarith
    have hgg : (0 : ℤ) ≤ ga * g := mul_nonneg hga0 hg0
    have hald : (0 : ℤ) ≤ al * de := mul_nonneg hal0 hde0
    have halg : (0 : ℤ) ≤ al * g := mul_nonneg hal0 hg0
    have e1 : 0 ≤ (2 * (ga * g * A)) * (B - 2 * q) := by
      refine mul_nonneg ?_ (by linarith)
      have := mul_nonneg hgg hA0
      linarith [this]
    have e2 : 0 ≤ (2 * (al * de * B)) * (A - 2 * p) := by
      refine mul_nonneg ?_ (by linarith)
      have := mul_nonneg hald hB0
      linarith [this]
    have hpq : 4 * (p * q) ≤ A * B := by
      nlinarith [mul_nonneg (sub_nonneg.2 hpA) hB0,
        mul_nonneg (by linarith : (0 : ℤ) ≤ 2 * p) (sub_nonneg.2 hqB)]
    have e3 : 0 ≤ (al * g) * (A * B - 4 * (p * q)) := mul_nonneg halg (by linarith)
    have hstep : 4 * (ga * de) + 2 * (g * ga) + 2 * (al * de) + g * al + 4 + 1 ≤ 4 * N :=
      hsize
    have hABpos : (0 : ℤ) ≤ A * B := mul_nonneg hA0 hB0
    have e4 : 0 ≤ (A * B) * (4 * N - 4 * (ga * de) - 2 * (ga * g) - 2 * (al * de) - al * g - 5) :=
      mul_nonneg hABpos (by linarith)
    have e5 : (1 : ℤ) ≤ A * B := by nlinarith [hA1, hB1]
    linarith [e1, e2, e3, e4, e5]
  -- the strict spread inequality, now with no size hypothesis
  have hspread : ∀ (a b c d : ℕ), 2 ≤ a → a < c → c ≤ d → d < b → a * b = c * d →
      ∀ m : ℕ, pairMoment (m + 3) (c : ℤ) (d : ℤ) < pairMoment (m + 3) (a : ℤ) (b : ℤ) := by
    intro a b c d ha hac hcd hdb hprod m
    -- the size estimate holds unconditionally
    have hc3 : 3 ≤ c := by omega
    have hd3 : 3 ≤ d := le_trans hc3 hcd
    have h3c : 3 * c ≤ a * b := by rw [hprod]; nlinarith
    have h3d : 3 * d ≤ a * b := by rw [hprod]; nlinarith
    have hN9 : 9 ≤ a * b := by rw [hprod]; nlinarith
    have h8 : 12 * b + 3 * a + 12 < 8 * (a * b) := by
      rcases Nat.lt_or_ge a 3 with hlt | hge
      · have ha2 : a = 2 := by omega
        subst ha2
        omega
      · have h3b : 3 * b ≤ a * b := Nat.mul_le_mul_right b hge
        have hb3 : 3 ≤ b := by omega
        linarith
    have hsizeN : 4 * b + 2 * c + 2 * d + a + 4 < 4 * (a * b) := by linarith
    -- the gcd parameterisation of the two factorisations
    have hbpos : 0 < b := by omega
    have hGpos : 0 < Nat.gcd a c := Nat.gcd_pos_of_pos_left c (by omega)
    set G := Nat.gcd a c with hGdef
    have hGa : G ∣ a := Nat.gcd_dvd_left a c
    have hGc : G ∣ c := Nat.gcd_dvd_right a c
    set al := a / G with haldef
    set ga := c / G with hgadef
    have hae : a = G * al := (Nat.mul_div_cancel' hGa).symm
    have hce : c = G * ga := (Nat.mul_div_cancel' hGc).symm
    have hcop : Nat.Coprime al ga := Nat.coprime_div_gcd_div_gcd hGpos
    have halpos : 0 < al := by
      rcases Nat.eq_zero_or_pos al with h0 | h0
      · rw [h0, mul_zero] at hae; omega
      · exact h0
    have hgapos : 0 < ga := by
      rcases Nat.eq_zero_or_pos ga with h0 | h0
      · rw [h0, mul_zero] at hce; omega
      · exact h0
    have hcancel : al * b = ga * d := by
      have hgg : G * (al * b) = G * (ga * d) := by
        calc G * (al * b) = (G * al) * b := by ring
          _ = a * b := by rw [← hae]
          _ = c * d := hprod
          _ = (G * ga) * d := by rw [← hce]
          _ = G * (ga * d) := by ring
      exact Nat.eq_of_mul_eq_mul_left hGpos hgg
    have hgadvd : ga ∣ b := by
      have hdvd : ga ∣ al * b := ⟨d, hcancel⟩
      exact (Nat.Coprime.dvd_of_dvd_mul_left hcop.symm hdvd)
    set de := b / ga with hdedef
    have hbe : b = ga * de := (Nat.mul_div_cancel' hgadvd).symm
    have hdepos : 0 < de := by
      rcases Nat.eq_zero_or_pos de with h0 | h0
      · rw [h0, mul_zero] at hbe; omega
      · exact h0
    have hdeq : d = al * de := by
      have hgg : ga * (al * de) = ga * d := by
        calc ga * (al * de) = al * (ga * de) := by ring
          _ = al * b := by rw [← hbe]
          _ = ga * d := hcancel
      exact (Nat.eq_of_mul_eq_mul_left hgapos hgg).symm
    have halga : al < ga := by
      have hlt : G * al < G * ga := by rw [← hae, ← hce]; exact hac
      exact lt_of_mul_lt_mul_left hlt (Nat.zero_le G)
    have hGde : G < de := by
      have h1 : G * ga ≤ al * de := by rw [← hce, ← hdeq]; exact hcd
      have h2 : al * de < ga * de := Nat.mul_lt_mul_of_lt_of_le halga (le_refl de) hdepos
      have h3 : G * ga < ga * de := lt_of_le_of_lt h1 h2
      have h4 : ga * G < ga * de := by linarith [h3, Nat.mul_comm G ga]
      exact lt_of_mul_lt_mul_left h4 (Nat.zero_le ga)
    -- cast the four factorisation identities to ℤ
    have cA : (a : ℤ) = (G : ℤ) * al := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hae
    have cB : (b : ℤ) = (ga : ℤ) * de := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hbe
    have cC : (c : ℤ) = (G : ℤ) * ga := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hce
    have cD : (d : ℤ) = (al : ℤ) * de := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hdeq
    have hsizeZ : 4 * ((ga : ℤ) * de) + 2 * ((G : ℤ) * ga) + 2 * ((al : ℤ) * de)
        + (G : ℤ) * al + 4 < 4 * ((G : ℤ) * al * ga * de) := by
      have hz : 4 * (b : ℤ) + 2 * (c : ℤ) + 2 * (d : ℤ) + (a : ℤ) + 4 < 4 * ((a : ℤ) * b) := by
        exact_mod_cast hsizeN
      rw [cA, cB, cC, cD] at hz
      rw [show 4 * ((G : ℤ) * al * ga * de) = 4 * (((G : ℤ) * al) * ((ga : ℤ) * de)) by ring]
      exact hz
    -- the homogeneous-sum facts
    have hpos : ∀ (n : ℕ) (x y : ℤ), 1 ≤ x → 1 ≤ y → 1 ≤ hSum n x y := by
      intro n
      induction n with
      | zero => intro x y _ _; simp [hSum]
      | succ n ih =>
        intro x y hx hy
        have hprev := ih x y hx hy
        have hyp : 1 ≤ y ^ (n + 1) := one_le_pow₀ hy
        rw [hSum]
        nlinarith
    have hxle : ∀ (n : ℕ) (x y : ℤ), 1 ≤ x → 1 ≤ y → x ^ n ≤ hSum n x y := by
      intro n
      induction n with
      | zero => intro x y _ _; simp [hSum]
      | succ n ih =>
        intro x y hx hy
        have hprev := ih x y hx hy
        have hyp : 1 ≤ y ^ (n + 1) := one_le_pow₀ hy
        have hkey : 0 ≤ x * (hSum n x y - x ^ n) := mul_nonneg (by linarith) (by linarith)
        have hx1 : x ^ (n + 1) = x * x ^ n := by ring
        rw [hSum]
        linarith [hkey, hyp, hx1]
    have hdom : ∀ (n : ℕ) (x y : ℤ), 1 ≤ x → 1 ≤ y →
        x ^ (n + 1) + y ^ (n + 1) ≤ hSum (n + 1) x y := by
      intro n x y hx hy
      have h1 := hxle n x y hx hy
      have hkey : 0 ≤ x * (hSum n x y - x ^ n) := mul_nonneg (by linarith) (by linarith)
      have hx1 : x ^ (n + 1) = x * x ^ n := by ring
      rw [hSum]
      linarith [hkey, hx1]
    have hgaZ : (1 : ℤ) ≤ (ga : ℤ) := by exact_mod_cast hgapos
    have halZ : (1 : ℤ) ≤ (al : ℤ) := by exact_mod_cast halpos
    have hdeZ : (1 : ℤ) ≤ (de : ℤ) := by exact_mod_cast hdepos
    have hGZ : (1 : ℤ) ≤ (G : ℤ) := by exact_mod_cast hGpos
    have halgaZ : (al : ℤ) < (ga : ℤ) := by exact_mod_cast halga
    have hGdeZ : (G : ℤ) < (de : ℤ) := by exact_mod_cast hGde
    have hA1 : (1 : ℤ) ≤ hSum (m + 1) (ga : ℤ) (al : ℤ) := hpos _ _ _ hgaZ halZ
    have hB1 : (1 : ℤ) ≤ hSum (m + 1) (de : ℤ) (G : ℤ) := hpos _ _ _ hdeZ hGZ
    have hp1 : (1 : ℤ) ≤ (al : ℤ) ^ (m + 1) := one_le_pow₀ halZ
    have hq1 : (1 : ℤ) ≤ (G : ℤ) ^ (m + 1) := one_le_pow₀ hGZ
    have hplt : (al : ℤ) ^ (m + 1) < (ga : ℤ) ^ (m + 1) :=
      pow_lt_pow_left₀ halgaZ (by linarith) (Nat.succ_ne_zero m)
    have hqlt : (G : ℤ) ^ (m + 1) < (de : ℤ) ^ (m + 1) :=
      pow_lt_pow_left₀ hGdeZ (by linarith) (Nat.succ_ne_zero m)
    have hpA : 2 * (al : ℤ) ^ (m + 1) ≤ hSum (m + 1) (ga : ℤ) (al : ℤ) := by
      have := hdom m (ga : ℤ) (al : ℤ) hgaZ halZ
      linarith
    have hqB : 2 * (G : ℤ) ^ (m + 1) ≤ hSum (m + 1) (de : ℤ) (G : ℤ) := by
      have := hdom m (de : ℤ) (G : ℤ) hdeZ hGZ
      linarith
    -- the two top sums split off their leading term
    have hCeq : hSum (m + 2) (ga : ℤ) (al : ℤ)
        = (ga : ℤ) * hSum (m + 1) (ga : ℤ) (al : ℤ) + (al : ℤ) * (al : ℤ) ^ (m + 1) := by
      rw [show m + 2 = (m + 1) + 1 from rfl, hSum, pow_succ, mul_comm ((al : ℤ) ^ (m + 1)) (al : ℤ)]
    have hDeq : hSum (m + 2) (de : ℤ) (G : ℤ)
        = (de : ℤ) * hSum (m + 1) (de : ℤ) (G : ℤ) + (G : ℤ) * (G : ℤ) ^ (m + 1) := by
      rw [show m + 2 = (m + 1) + 1 from rfl, hSum, pow_succ, mul_comm ((G : ℤ) ^ (m + 1)) (G : ℤ)]
    have hbracket : 0 < ((G : ℤ) * al * ga * de) * hSum (m + 1) (ga : ℤ) (al : ℤ)
        * hSum (m + 1) (de : ℤ) (G : ℤ)
        - hSum (m + 2) (ga : ℤ) (al : ℤ) * hSum (m + 2) (de : ℤ) (G : ℤ) - 1 := by
      have hc := core ((G : ℤ) * al * ga * de) (ga : ℤ) (de : ℤ) (al : ℤ) (G : ℤ)
        (hSum (m + 1) (ga : ℤ) (al : ℤ)) (hSum (m + 1) (de : ℤ) (G : ℤ))
        ((al : ℤ) ^ (m + 1)) ((G : ℤ) ^ (m + 1))
        hA1 hB1 hp1 hq1 (by linarith) (by linarith) (by linarith) (by linarith)
        hpA hqB rfl hsizeZ
      rw [hCeq, hDeq]
      linarith [hc]
    -- the difference of the two moments factors through the bracket
    have hfac : ∀ (n : ℕ) (x y : ℤ), (x - y) * hSum n x y = x ^ (n + 1) - y ^ (n + 1) := by
      intro n
      induction n with
      | zero => intro x y; simp [hSum]
      | succ n ih =>
        intro x y
        rw [hSum]
        linear_combination x * ih x y
    have f1 : ((ga : ℤ) - al) * hSum (m + 1) (ga : ℤ) (al : ℤ)
        = (ga : ℤ) ^ (m + 2) - (al : ℤ) ^ (m + 2) := hfac (m + 1) _ _
    have f2 : ((de : ℤ) - G) * hSum (m + 1) (de : ℤ) (G : ℤ)
        = (de : ℤ) ^ (m + 2) - (G : ℤ) ^ (m + 2) := hfac (m + 1) _ _
    have f3 : ((ga : ℤ) - al) * hSum (m + 2) (ga : ℤ) (al : ℤ)
        = (ga : ℤ) ^ (m + 3) - (al : ℤ) ^ (m + 3) := hfac (m + 2) _ _
    have f4 : ((de : ℤ) - G) * hSum (m + 2) (de : ℤ) (G : ℤ)
        = (de : ℤ) ^ (m + 3) - (G : ℤ) ^ (m + 3) := hfac (m + 2) _ _
    have hid : pairMoment (m + 3) ((G : ℤ) * al) ((ga : ℤ) * de)
        - pairMoment (m + 3) ((G : ℤ) * ga) ((al : ℤ) * de)
        = ((ga : ℤ) - al) * ((de : ℤ) - G)
          * (((G : ℤ) * al * ga * de) * hSum (m + 1) (ga : ℤ) (al : ℤ)
            * hSum (m + 1) (de : ℤ) (G : ℤ)
            - hSum (m + 2) (ga : ℤ) (al : ℤ) * hSum (m + 2) (de : ℤ) (G : ℤ) - 1) := by
      have hring : pairMoment (m + 3) ((G : ℤ) * al) ((ga : ℤ) * de)
          - pairMoment (m + 3) ((G : ℤ) * ga) ((al : ℤ) * de)
          = ((G : ℤ) * al * ga * de) * ((ga : ℤ) ^ (m + 2) - (al : ℤ) ^ (m + 2))
              * ((de : ℤ) ^ (m + 2) - (G : ℤ) ^ (m + 2))
            - ((ga : ℤ) ^ (m + 3) - (al : ℤ) ^ (m + 3))
              * ((de : ℤ) ^ (m + 3) - (G : ℤ) ^ (m + 3))
            - ((ga : ℤ) - al) * ((de : ℤ) - G) := by
        unfold pairMoment
        ring
      rw [hring, ← f1, ← f2, ← f3, ← f4]
      ring
    have hposfac : 0 < ((ga : ℤ) - al) * ((de : ℤ) - G) :=
      mul_pos (by linarith) (by linarith)
    have hmulpos : 0 < ((ga : ℤ) - al) * ((de : ℤ) - G)
        * (((G : ℤ) * al * ga * de) * hSum (m + 1) (ga : ℤ) (al : ℤ)
            * hSum (m + 1) (de : ℤ) (G : ℤ)
            - hSum (m + 2) (ga : ℤ) (al : ℤ) * hSum (m + 2) (de : ℤ) (G : ℤ) - 1) :=
      mul_pos hposfac hbracket
    rw [cA, cB, cC, cD]
    linarith [hid, hmulpos]
  -- trichotomy
  have hsmall : ∀ (a b c d : ℕ), 0 < a → a < c → a * b = c * d → 0 < d → d < b := by
    intro a b c d hapos hac hprod hdpos
    have h1 : a * d < c * d := Nat.mul_lt_mul_of_lt_of_le hac (le_refl d) hdpos
    have h2 : a * d < a * b := by rw [hprod]; exact h1
    exact lt_of_mul_lt_mul_left h2 (Nat.zero_le a)
  have hapos : 0 < a := by omega
  have hcpos : 0 < c := by omega
  have hbpos : 0 < b := by omega
  have hdpos : 0 < d := by omega
  rcases lt_trichotomy a c with hlt | heq | hgt
  · exfalso
    have hdb : d < b := hsmall a b c d hapos hlt hprod hdpos
    have hstrict := hspread a b c d ha hlt hcd hdb hprod m
    rw [hm] at hstrict
    exact lt_irrefl _ hstrict
  · subst heq
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hapos hprod⟩
  · exfalso
    have hbd : b < d := hsmall c d a b hcpos hgt hprod.symm hbpos
    have hstrict := hspread c d a b hc hgt hab hbd hprod.symm m
    rw [← hm] at hstrict
    exact lt_irrefl _ hstrict
