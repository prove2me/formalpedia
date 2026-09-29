-- Prove2me | solution 2 for GCDMoment.pairMoment_injective_of_three_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T21:45:44.784298+00:00
-- url     : https://prove2.me/submissions/bf803308-a484-4853-945b-6a10b3909734

import Mathlib
import Definitions.Def_Novelty_GCDMomentHigherInversion
import Definitions.Def_Novelty_GCDMomentPairInversion

set_option maxHeartbeats 1600000 in
open GCDMoment in
theorem solution {a b c d : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) (hc : 2 ≤ c)
    (hcd : c ≤ d) (hprod : a * b = c * d) (hN : 31 ≤ a * b) (m : ℕ)
    (hm : pairMoment (m + 3) (a : ℤ) (b : ℤ) = pairMoment (m + 3) (c : ℤ) (d : ℤ)) :
    a = c ∧ b = d := by
  classical
  -- the strict spread inequality, proved for a general pair of factorisations
  have hspread : ∀ (a b c d : ℕ), 2 ≤ a → a < c → c ≤ d → d < b → a * b = c * d →
      a + b + c + d < a * b → ∀ m : ℕ,
      pairMoment (m + 3) (c : ℤ) (d : ℤ) < pairMoment (m + 3) (a : ℤ) (b : ℤ) := by
    intro a b c d ha hac hcd hdb hprod hsum m
    have hparam : ∀ (g al ga de : ℤ), 1 ≤ g → 1 ≤ al → 1 ≤ ga → 1 ≤ de → al < ga → g < de →
        (g * al + ga * de + g * ga + al * de < g * al * ga * de) →
        pairMoment (m + 3) (g * ga) (al * de) < pairMoment (m + 3) (g * al) (ga * de) := by
      intro g al ga de hg hal hga hde halga hgde hsum
      have hbracket : 0 < (g * al * ga * de) * hSum (m + 1) ga al * hSum (m + 1) de g
          - hSum (m + 2) ga al * hSum (m + 2) de g - 1 := by
        -- the homogeneous sums are positive and dominate their last term
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
        have hyle : ∀ (n : ℕ) (x y : ℤ), 1 ≤ x → 1 ≤ y → y ^ n ≤ hSum n x y := by
          intro n
          induction n with
          | zero => intro x y _ _; simp [hSum]
          | succ n ih =>
            intro x y hx hy
            have hprev := hpos n x y hx hy
            rw [hSum]
            nlinarith
        have hstep : ∀ (n : ℕ) (x y : ℤ), 1 ≤ x → 1 ≤ y →
            hSum (n + 1) x y ≤ (x + y) * hSum n x y := by
          intro n x y hx hy
          have hprev := hpos n x y hx hy
          have hy1 : y ^ (n + 1) ≤ y * hSum n x y := by
            have hyn := hyle n x y hx hy
            have : y ^ (n + 1) = y * y ^ n := by ring
            rw [this]
            nlinarith
          rw [hSum]
          nlinarith
        have hge2 : ∀ (n : ℕ) (x y : ℤ), 1 ≤ x → 1 ≤ y → 2 ≤ hSum (n + 1) x y := by
          intro n x y hx hy
          have hprev := hpos n x y hx hy
          have hyp : 1 ≤ y ^ (n + 1) := one_le_pow₀ hy
          rw [hSum]
          nlinarith
        -- abbreviations
        set A := hSum (m + 1) ga al with hAdef
        set B := hSum (m + 1) de g with hBdef
        set C := hSum (m + 2) ga al with hCdef
        set D := hSum (m + 2) de g with hDdef
        have hA1 : 1 ≤ A := hpos _ _ _ hga hal
        have hB1 : 1 ≤ B := hpos _ _ _ hde hg
        have hA2 : 2 ≤ A := hge2 _ _ _ hga hal
        have hC1 : 1 ≤ C := hpos _ _ _ hga hal
        have hD1 : 1 ≤ D := hpos _ _ _ hde hg
        have hCle : C ≤ (ga + al) * A := hstep _ _ _ hga hal
        have hDle : D ≤ (de + g) * B := hstep _ _ _ hde hg
        have hgap : (ga + al) * (de + g) + 1 ≤ g * al * ga * de := by nlinarith [hsum]
        have hABpos : (0 : ℤ) ≤ A * B := by nlinarith [hA1, hB1]
        have h1 : C * D ≤ ((ga + al) * (de + g)) * (A * B) := by
          have hmul := mul_le_mul hCle hDle (by linarith) (by nlinarith [hA1, hga, hal])
          calc C * D ≤ ((ga + al) * A) * ((de + g) * B) := hmul
            _ = ((ga + al) * (de + g)) * (A * B) := by ring
        have h2 : ((ga + al) * (de + g)) * (A * B) + (A * B) ≤ (g * al * ga * de) * (A * B) := by
          have hmul := mul_le_mul_of_nonneg_right hgap hABpos
          calc ((ga + al) * (de + g)) * (A * B) + (A * B)
              = ((ga + al) * (de + g) + 1) * (A * B) := by ring
            _ ≤ (g * al * ga * de) * (A * B) := hmul
        have h3 : (2 : ℤ) ≤ A * B := by nlinarith [hA2, hB1]
        have hassoc : (g * al * ga * de) * A * B = (g * al * ga * de) * (A * B) := by ring
        rw [hassoc]
        linarith [h1, h2, h3]
      -- the factorisation of a power difference
      have hfac : ∀ (n : ℕ) (x y : ℤ), (x - y) * hSum n x y = x ^ (n + 1) - y ^ (n + 1) := by
        intro n
        induction n with
        | zero =>
          intro x y
          simp [hSum]
        | succ n ih =>
          intro x y
          rw [hSum]
          linear_combination x * ih x y
      have h1 : (ga - al) * hSum (m + 1) ga al = ga ^ (m + 2) - al ^ (m + 2) := by
        have hx := hfac (m + 1) ga al
        rw [show m + 1 + 1 = m + 2 from rfl] at hx
        exact hx
      have h2 : (de - g) * hSum (m + 1) de g = de ^ (m + 2) - g ^ (m + 2) := by
        have hx := hfac (m + 1) de g
        rw [show m + 1 + 1 = m + 2 from rfl] at hx
        exact hx
      have h3 : (ga - al) * hSum (m + 2) ga al = ga ^ (m + 3) - al ^ (m + 3) := by
        have hx := hfac (m + 2) ga al
        rw [show m + 2 + 1 = m + 3 from rfl] at hx
        exact hx
      have h4 : (de - g) * hSum (m + 2) de g = de ^ (m + 3) - g ^ (m + 3) := by
        have hx := hfac (m + 2) de g
        rw [show m + 2 + 1 = m + 3 from rfl] at hx
        exact hx
      -- the difference of the two pair moments factors through the bracket
      have hid : pairMoment (m + 3) (g * al) (ga * de) - pairMoment (m + 3) (g * ga) (al * de)
          = (ga - al) * (de - g) * ((g * al * ga * de) * hSum (m + 1) ga al * hSum (m + 1) de g
            - hSum (m + 2) ga al * hSum (m + 2) de g - 1) := by
        have hring : pairMoment (m + 3) (g * al) (ga * de) - pairMoment (m + 3) (g * ga) (al * de)
            = (g * al * ga * de) * (ga ^ (m + 2) - al ^ (m + 2)) * (de ^ (m + 2) - g ^ (m + 2))
              - (ga ^ (m + 3) - al ^ (m + 3)) * (de ^ (m + 3) - g ^ (m + 3))
              - (ga - al) * (de - g) := by
          unfold pairMoment
          ring
        rw [hring, ← h1, ← h2, ← h3, ← h4]
        ring
      have hposfac : 0 < (ga - al) * (de - g) := mul_pos (by linarith) (by linarith)
      nlinarith [hid, hbracket, hposfac]
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
    -- the inequalities in the parameters
    have halga : al < ga := by
      have : G * al < G * ga := by rw [← hae, ← hce]; exact hac
      exact lt_of_mul_lt_mul_left this (Nat.zero_le G)
    have hGde : G < de := by
      have h1 : G * ga ≤ al * de := by rw [← hce, ← hdeq]; exact hcd
      have h2 : al * de < ga * de := by
        exact Nat.mul_lt_mul_of_lt_of_le halga (le_refl de) hdepos
      have h3 : G * ga < ga * de := lt_of_le_of_lt h1 h2
      have h4 : ga * G < ga * de := by linarith [h3, Nat.mul_comm G ga]
      exact lt_of_mul_lt_mul_left h4 (Nat.zero_le ga)
    -- transport to ℤ and apply the parametric inequality
    have hcastsum : (G : ℤ) * al + (ga : ℤ) * de + (G : ℤ) * ga + (al : ℤ) * de
        < (G : ℤ) * al * ga * de := by
      have hz : (a : ℤ) + b + c + d < (a : ℤ) * b := by exact_mod_cast hsum
      rw [show (a : ℤ) = (G : ℤ) * al by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hae,
        show (b : ℤ) = (ga : ℤ) * de by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hbe,
        show (c : ℤ) = (G : ℤ) * ga by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hce,
        show (d : ℤ) = (al : ℤ) * de by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hdeq] at hz
      linarith [hz]
    have hres := hparam (G : ℤ) (al : ℤ) (ga : ℤ) (de : ℤ)
      (by exact_mod_cast hGpos) (by exact_mod_cast halpos) (by exact_mod_cast hgapos)
      (by exact_mod_cast hdepos) (by exact_mod_cast halga) (by exact_mod_cast hGde) hcastsum
    rw [show (c : ℤ) = (G : ℤ) * ga by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hce,
      show (d : ℤ) = (al : ℤ) * de by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hdeq,
      show (a : ℤ) = (G : ℤ) * al by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hae,
      show (b : ℤ) = (ga : ℤ) * de by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hbe]
    exact hres

  -- the size hypothesis forces the sum of the four factors below the product
  have key : ∀ (a b c d : ℕ), 2 ≤ a → a ≤ b → 2 ≤ c → c ≤ d → a * b = c * d →
      31 ≤ a * b → a < c → a + b + c + d < a * b := by
    intro a b c d ha hab hc hcd hprod hN hac
    have hb2 : 2 ≤ b := le_trans ha hab
    have hc3 : 3 ≤ c := by omega
    have hd3 : 3 ≤ d := le_trans hc3 hcd
    have h1 : 2 * (a + b) ≤ a * b + 4 := by
      obtain ⟨p, rfl⟩ : ∃ p, a = 2 + p := ⟨a - 2, by omega⟩
      obtain ⟨q, rfl⟩ : ∃ q, b = 2 + q := ⟨b - 2, by omega⟩
      nlinarith [Nat.zero_le (p * q)]
    have h2 : 3 * (c + d) ≤ a * b + 9 := by
      rw [hprod]
      obtain ⟨u, rfl⟩ : ∃ u, c = 3 + u := ⟨c - 3, by omega⟩
      obtain ⟨v, rfl⟩ : ∃ v, d = 3 + v := ⟨d - 3, by omega⟩
      nlinarith [Nat.zero_le (u * v)]
    linarith
  -- the two factorisations must agree on the smaller factor
  have hsmall : ∀ (a b c d : ℕ), 0 < a → a < c → a * b = c * d → 0 < d → d < b := by
    intro a b c d hapos hac hprod hdpos
    have h1 : a * d < c * d := Nat.mul_lt_mul_of_lt_of_le hac (le_refl d) hdpos
    have h2 : a * d < a * b := by rw [hprod]; exact h1
    exact lt_of_mul_lt_mul_left h2 (Nat.zero_le a)
  have hapos : 0 < a := by omega
  have hcpos : 0 < c := by omega
  have hbpos : 0 < b := by omega
  have hdpos : 0 < d := by omega
  have hNcd : 31 ≤ c * d := by rw [← hprod]; exact hN
  rcases lt_trichotomy a c with hlt | heq | hgt
  · exfalso
    have hdb : d < b := hsmall a b c d hapos hlt hprod hdpos
    have hs := key a b c d ha hab hc hcd hprod hN hlt
    have hstrict := hspread a b c d ha hlt hcd hdb hprod hs m
    rw [hm] at hstrict
    exact lt_irrefl _ hstrict
  · subst heq
    refine ⟨rfl, ?_⟩
    exact Nat.eq_of_mul_eq_mul_left hapos hprod
  · exfalso
    have hbd : b < d := hsmall c d a b hcpos hgt hprod.symm hbpos
    have hs := key c d a b hc hcd ha hab hprod.symm hNcd hgt
    have hstrict := hspread c d a b hc hgt hab hbd hprod.symm hs m
    rw [← hm] at hstrict
    exact lt_irrefl _ hstrict
