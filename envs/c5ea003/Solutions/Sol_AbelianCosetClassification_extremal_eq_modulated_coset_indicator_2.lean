-- Prove2me | solution 2 for AbelianCosetClassification.extremal_eq_modulated_coset_indicator
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T22:09:59.45401+00:00
-- url     : https://prove2.me/submissions/e5f46850-f555-434e-832e-efa554574917

import Mathlib
import Definitions.Def_Bridges_AbelianCosetClassification
import Definitions.Def_Bridges_CosetClassification
import Definitions.Def_Bridges_FiniteAbelianUncertainty

set_option maxHeartbeats 1000000 in
open Finset FiniteAbelianUncertainty AbelianCosetClassification in
theorem solution {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {f : G → ℂ} (hf : f ≠ 0)
    (hext : (gsupport f).card * (dsupport (gdft f)).card = Fintype.card G) :
    ∃ (K : Finset G) (a₀ : G) (psi₀ : AddChar G ℂ) (c : ℂ),
      c ≠ 0 ∧ (0 : G) ∈ K ∧ (∀ x ∈ K, ∀ y ∈ K, x + y ∈ K) ∧
        K.card = (gsupport f).card ∧
        ∀ a, f a = if a - a₀ ∈ K then c * psi₀ a else 0 := by
  classical
  -- characters are conjugated by negation and have unit modulus
  have hconj : ∀ (ps : AddChar G ℂ) (x : G), (starRingEnd ℂ) (ps x) = ps (-x) := by
    intro ps x
    rw [AddChar.map_neg_eq_inv, AddChar.inv_apply_eq_conj]
  have hmul1 : ∀ (ps : AddChar G ℂ) (x : G), ps x * (starRingEnd ℂ) (ps x) = 1 := by
    intro ps x
    rw [hconj, ← AddChar.map_add_eq_mul]
    simp
  have hnorm1 : ∀ (ps : AddChar G ℂ) (x : G), ‖ps x‖ = 1 := by
    intro ps x
    have h5 : ‖ps x‖ * ‖ps x‖ = 1 := by
      have h := hmul1 ps x
      have hn : ‖ps x * (starRingEnd ℂ) (ps x)‖ = 1 := by rw [h]; simp
      rwa [norm_mul, RCLike.norm_conj] at hn
    nlinarith [norm_nonneg (ps x), h5]
  set L1 : ℝ := ∑ a, ‖f a‖ with hL1def
  set L2 : ℝ := ∑ a, ‖f a‖ ^ 2 with hL2def
  have hL1nn : 0 ≤ L1 := Finset.sum_nonneg (fun a _ => norm_nonneg _)
  have hL2pos : 0 < L2 := by
    obtain ⟨a, ha⟩ : ∃ a, f a ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hf (funext hc)
    rw [hL2def]
    refine Finset.sum_pos' (fun i _ => by positivity) ⟨a, Finset.mem_univ a, ?_⟩
    have hp : 0 < ‖f a‖ := norm_pos_iff.2 ha
    positivity
  -- Parseval for the group Fourier transform
  have hParseval : ∑ ps : AddChar G ℂ, ‖gdft f ps‖ ^ 2 = (Fintype.card G : ℝ) * L2 := by
    have key : ∀ ps : AddChar G ℂ, ((‖gdft f ps‖ ^ 2 : ℝ) : ℂ)
        = ∑ a, ∑ b, ps (b - a) * (f a * (starRingEnd ℂ) (f b)) := by
      intro ps
      have h0 : ((‖gdft f ps‖ ^ 2 : ℝ) : ℂ) = gdft f ps * (starRingEnd ℂ) (gdft f ps) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [h0]
      simp only [gdft, map_sum, map_mul]
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
      rw [hconj, neg_neg]
      have hchar : ps (-a) * ps b = ps (b - a) := by
        rw [← AddChar.map_add_eq_mul]
        congr 1
        abel
      calc ps (-a) * f a * (ps b * (starRingEnd ℂ) (f b))
          = (ps (-a) * ps b) * (f a * (starRingEnd ℂ) (f b)) := by ring
        _ = ps (b - a) * (f a * (starRingEnd ℂ) (f b)) := by rw [hchar]
    have hswap : ∑ ps : AddChar G ℂ, ((‖gdft f ps‖ ^ 2 : ℝ) : ℂ)
        = ∑ a, ∑ b, (∑ ps : AddChar G ℂ, ps (b - a)) * (f a * (starRingEnd ℂ) (f b)) := by
      simp only [key]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [← Finset.sum_mul]
    have hdiag : ∑ a, ∑ b, (∑ ps : AddChar G ℂ, ps (b - a)) * (f a * (starRingEnd ℂ) (f b))
        = ((Fintype.card G : ℝ) : ℂ) * ((L2 : ℝ) : ℂ) := by
      have hin : ∀ a : G, ∑ b, (∑ ps : AddChar G ℂ, ps (b - a)) * (f a * (starRingEnd ℂ) (f b))
          = (Fintype.card G : ℂ) * ((‖f a‖ ^ 2 : ℝ) : ℂ) := by
        intro a
        rw [Finset.sum_eq_single a]
        · simp only [sub_self, AddChar.sum_apply_eq_ite]
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
          push_cast
          ring
        · intro b _ hb
          have hne : b - a ≠ 0 := sub_ne_zero.2 hb
          simp [AddChar.sum_apply_eq_ite, hne]
        · intro h
          exact absurd (Finset.mem_univ a) h
      rw [Finset.sum_congr rfl (fun a _ => hin a), ← Finset.mul_sum]
      rw [hL2def]
      push_cast
      ring
    have hfinal : ((∑ ps : AddChar G ℂ, ‖gdft f ps‖ ^ 2 : ℝ) : ℂ)
        = (((Fintype.card G : ℝ) * L2 : ℝ) : ℂ) := by
      push_cast
      push_cast at hswap hdiag
      rw [hswap, hdiag]
    exact_mod_cast hfinal
  -- every Fourier coefficient is bounded by the ℓ¹ norm
  have hbound : ∀ ps : AddChar G ℂ, ‖gdft f ps‖ ≤ L1 := by
    intro ps
    have h1 : ‖gdft f ps‖ ≤ ∑ a, ‖ps (-a) * f a‖ := by
      rw [gdft]; exact norm_sum_le _ _
    have h2 : ∑ a, ‖ps (-a) * f a‖ = L1 := by
      rw [hL1def]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [norm_mul, hnorm1, one_mul]
    linarith [h1, h2.le, h2.ge]
  -- Cauchy–Schwarz on the support
  have hsupp1 : L1 = ∑ a ∈ gsupport f, ‖f a‖ := by
    rw [hL1def]
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro a _ ha
    simp only [gsupport, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at ha
    rw [ha]; simp
  have hsupp2 : L2 = ∑ a ∈ gsupport f, ‖f a‖ ^ 2 := by
    rw [hL2def]
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro a _ ha
    simp only [gsupport, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at ha
    rw [ha]; simp
  have hCS : L1 ^ 2 ≤ ((gsupport f).card : ℝ) * L2 := by
    rw [hsupp1, hsupp2]
    exact sq_sum_le_card_mul_sum_sq
  -- the Fourier mass lives on the spectrum
  have hDS : ∑ ps ∈ dsupport (gdft f), ‖gdft f ps‖ ^ 2 = (Fintype.card G : ℝ) * L2 := by
    rw [← hParseval]
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro ps _ hps
    simp only [dsupport, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hps
    rw [hps]; simp
  have hterm : ∀ ps ∈ dsupport (gdft f), ‖gdft f ps‖ ^ 2 ≤ L1 ^ 2 := by
    intro ps _
    have := hbound ps
    nlinarith [norm_nonneg (gdft f ps), hL1nn]
  have hsum_le : ∑ ps ∈ dsupport (gdft f), ‖gdft f ps‖ ^ 2
      ≤ ((dsupport (gdft f)).card : ℝ) * L1 ^ 2 := by
    calc ∑ ps ∈ dsupport (gdft f), ‖gdft f ps‖ ^ 2
        ≤ ∑ _ps ∈ dsupport (gdft f), L1 ^ 2 := Finset.sum_le_sum hterm
      _ = ((dsupport (gdft f)).card : ℝ) * L1 ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hcardEq : ((gsupport f).card : ℝ) * ((dsupport (gdft f)).card : ℝ)
      = (Fintype.card G : ℝ) := by exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hext
  have hchain : ((dsupport (gdft f)).card : ℝ) * L1 ^ 2 ≤ (Fintype.card G : ℝ) * L2 := by
    have hmul := mul_le_mul_of_nonneg_left hCS
      (Nat.cast_nonneg (α := ℝ) (dsupport (gdft f)).card)
    calc ((dsupport (gdft f)).card : ℝ) * L1 ^ 2
        ≤ ((dsupport (gdft f)).card : ℝ) * (((gsupport f).card : ℝ) * L2) := hmul
      _ = (((gsupport f).card : ℝ) * ((dsupport (gdft f)).card : ℝ)) * L2 := by ring
      _ = (Fintype.card G : ℝ) * L2 := by rw [hcardEq]
  -- hence every coefficient on the spectrum attains the bound
  have heach : ∀ ps ∈ dsupport (gdft f), ‖gdft f ps‖ ^ 2 = L1 ^ 2 := by
    intro ps hps
    by_contra hne
    have hlt : ‖gdft f ps‖ ^ 2 < L1 ^ 2 := lt_of_le_of_ne (hterm ps hps) hne
    have hstrict : ∑ q ∈ dsupport (gdft f), ‖gdft f q‖ ^ 2
        < ∑ _q ∈ dsupport (gdft f), L1 ^ 2 :=
      Finset.sum_lt_sum hterm ⟨ps, hps, hlt⟩
    rw [Finset.sum_const, nsmul_eq_mul, hDS] at hstrict
    linarith [hchain]
  -- phase rigidity, uniformly over the spectrum
  have hphase : ∀ ps ∈ dsupport (gdft f), ∀ a : G,
      ps (-a) * f a = (‖f a‖ : ℂ) * (gdft f ps / ((‖gdft f ps‖ : ℝ) : ℂ)) := by
    intro ps hps a
    have hL1eq : ‖gdft f ps‖ = L1 := by
      have h2 := heach ps hps
      nlinarith [norm_nonneg (gdft f ps), hL1nn, h2]
    -- the Fourier coefficient is nonzero, so the unit phase is defined
    have hSne : gdft f ps ≠ 0 := by
      simp only [dsupport, Finset.mem_filter, Finset.mem_univ, true_and] at hps
      exact hps
    have hSpos : 0 < ‖gdft f ps‖ := norm_pos_iff.2 hSne
    set u : ℂ := gdft f ps / ((‖gdft f ps‖ : ℝ) : ℂ) with hudef
    have hcastne : ((‖gdft f ps‖ : ℝ) : ℂ) ≠ 0 := by
      simpa using ne_of_gt hSpos
    -- `conj u * S` is the real number `‖S‖`
    have hkeyS : (starRingEnd ℂ) u * gdft f ps = ((‖gdft f ps‖ : ℝ) : ℂ) := by
      rw [hudef, map_div₀, Complex.conj_ofReal]
      field_simp
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    -- the terms of the sum, and the equality in the triangle inequality
    have hsumterm : ∑ a, ((starRingEnd ℂ) u * (ps (-a) * f a)).re = ‖gdft f ps‖ := by
      have h1 : ∑ a, ((starRingEnd ℂ) u * (ps (-a) * f a))
          = (starRingEnd ℂ) u * gdft f ps := by
        rw [gdft, Finset.mul_sum]
      have h2 : (∑ a, ((starRingEnd ℂ) u * (ps (-a) * f a))).re = ‖gdft f ps‖ := by
        rw [h1, hkeyS]; simp
      rw [← h2, Complex.re_sum]
    have hle : ∀ a : G, ((starRingEnd ℂ) u * (ps (-a) * f a)).re ≤ ‖f a‖ := by
      intro a
      have h1 := Complex.re_le_norm ((starRingEnd ℂ) u * (ps (-a) * f a))
      have hun : ‖(starRingEnd ℂ) u‖ = 1 := by
        rw [RCLike.norm_conj, hudef, norm_div, Complex.norm_real, norm_norm,
          div_self (ne_of_gt hSpos)]
      rw [norm_mul, hun, one_mul, norm_mul, hnorm1, one_mul] at h1
      exact h1
    have hzero : ∀ a : G, ((starRingEnd ℂ) u * (ps (-a) * f a)).re = ‖f a‖ := by
      intro a
      by_contra hne
      have hlt : ((starRingEnd ℂ) u * (ps (-a) * f a)).re < ‖f a‖ :=
        lt_of_le_of_ne (hle a) hne
      have hstrict : ∑ b, ((starRingEnd ℂ) u * (ps (-b) * f b)).re < ∑ b, ‖f b‖ :=
        Finset.sum_lt_sum (fun b _ => hle b) ⟨a, Finset.mem_univ a, hlt⟩
      rw [hsumterm, hL1eq, ← hL1def] at hstrict
      exact absurd rfl (ne_of_lt hstrict)
    -- a complex number whose real part equals its modulus is that nonnegative real
    have hw : (starRingEnd ℂ) u * (ps (-a) * f a) = ((‖f a‖ : ℝ) : ℂ) := by
      set w : ℂ := (starRingEnd ℂ) u * (ps (-a) * f a) with hwdef
      have hre : w.re = ‖f a‖ := hzero a
      have hnw : ‖w‖ = ‖f a‖ := by
        rw [hwdef, norm_mul, norm_mul, hnorm1]
        have hun : ‖(starRingEnd ℂ) u‖ = 1 := by
          rw [RCLike.norm_conj, hudef, norm_div, Complex.norm_real, norm_norm,
            div_self (ne_of_gt hSpos)]
        rw [hun]
        ring
      have hns : Complex.normSq w = w.re * w.re + w.im * w.im := Complex.normSq_apply w
      have hns2 : Complex.normSq w = ‖w‖ ^ 2 := Complex.normSq_eq_norm_sq w
      have hsq : w.im * w.im = 0 := by
        have h1 : w.re * w.re + w.im * w.im = ‖w‖ ^ 2 := by rw [← hns, hns2]
        rw [hre, hnw] at h1
        have h2 : ‖f a‖ ^ 2 = ‖f a‖ * ‖f a‖ := by ring
        linarith
      have him : w.im = 0 := mul_self_eq_zero.mp hsq
      refine Complex.ext ?_ ?_
      · rw [hre]; simp
      · rw [him]; simp
    -- multiply back by `u`
    have huu : u * (starRingEnd ℂ) u = 1 := by
      have hun : ‖u‖ = 1 := by
        rw [hudef, norm_div, Complex.norm_real, norm_norm, div_self (ne_of_gt hSpos)]
      have := Complex.mul_conj u
      rw [Complex.normSq_eq_norm_sq, hun] at this
      simpa using this
    calc ps (-a) * f a = (u * (starRingEnd ℂ) u) * (ps (-a) * f a) := by rw [huu, one_mul]
      _ = u * ((starRingEnd ℂ) u * (ps (-a) * f a)) := by ring
      _ = u * ((‖f a‖ : ℝ) : ℂ) := by rw [hw]
      _ = ((‖f a‖ : ℝ) : ℂ) * (gdft f ps / ((‖gdft f ps‖ : ℝ) : ℂ)) := by rw [hudef]; ring

  -- both cardinalities are positive, so Cauchy–Schwarz is an equality
  have hGpos : 0 < Fintype.card G := Fintype.card_pos
  have hSposN : 0 < (gsupport f).card := by
    rcases Nat.eq_zero_or_pos (gsupport f).card with h0 | h0
    · rw [h0, zero_mul] at hext; omega
    · exact h0
  have hDposN : 0 < (dsupport (gdft f)).card := by
    rcases Nat.eq_zero_or_pos (dsupport (gdft f)).card with h0 | h0
    · rw [h0, mul_zero] at hext; omega
    · exact h0
  have hsumEq : ∑ ps ∈ dsupport (gdft f), ‖gdft f ps‖ ^ 2
      = ((dsupport (gdft f)).card : ℝ) * L1 ^ 2 := by
    rw [Finset.sum_congr rfl heach, Finset.sum_const, nsmul_eq_mul]
  have hDposR : (0 : ℝ) < ((dsupport (gdft f)).card : ℝ) := by exact_mod_cast hDposN
  have hCSeq : L1 ^ 2 = ((gsupport f).card : ℝ) * L2 := by
    have h1 : ((dsupport (gdft f)).card : ℝ) * L1 ^ 2 = (Fintype.card G : ℝ) * L2 := by
      rw [← hsumEq, hDS]
    have h2 : ((dsupport (gdft f)).card : ℝ) * L1 ^ 2
        = ((dsupport (gdft f)).card : ℝ) * (((gsupport f).card : ℝ) * L2) := by
      rw [h1, ← hcardEq]; ring
    exact mul_left_cancel₀ (ne_of_gt hDposR) h2
  have hcardR : (0 : ℝ) < ((gsupport f).card : ℝ) := by exact_mod_cast hSposN
  have hcne : ((gsupport f).card : ℝ) ≠ 0 := ne_of_gt hcardR
  -- equality in Cauchy–Schwarz forces constant modulus on the support
  have hflat : ∀ p ∈ gsupport f, ‖f p‖ = L1 / ((gsupport f).card : ℝ) := by
    intro p hp
    set m : ℝ := L1 / ((gsupport f).card : ℝ) with hmdef
    have hzeroSum : ∑ q ∈ gsupport f, (‖f q‖ - m) ^ 2 = 0 := by
      have hexpand : ∑ q ∈ gsupport f, (‖f q‖ - m) ^ 2
          = (∑ q ∈ gsupport f, ‖f q‖ ^ 2) - 2 * m * (∑ q ∈ gsupport f, ‖f q‖)
            + ((gsupport f).card : ℝ) * m ^ 2 := by
        rw [Finset.sum_congr rfl (fun q _ =>
          (by ring : (‖f q‖ - m) ^ 2 = ‖f q‖ ^ 2 - 2 * m * ‖f q‖ + m ^ 2))]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
          Finset.sum_const, nsmul_eq_mul]
      rw [hexpand, ← hsupp1, ← hsupp2, hmdef]
      field_simp
      nlinarith [hCSeq]
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun q _ => sq_nonneg (‖f q‖ - m))).1 hzeroSum
    have hsq0 : (‖f p‖ - m) ^ 2 = 0 := hall p hp
    have hz : ‖f p‖ - m = 0 := by
      exact sq_eq_zero_iff.mp hsq0
    linarith
  -- every character of the spectrum transports the support the same way
  have hchar : ∀ ps ∈ dsupport (gdft f), ∀ a ∈ gsupport f, ∀ a' ∈ gsupport f,
      f a = ps (a - a') * f a' := by
    intro ps hps a ha a' ha'
    have hflateq : ‖f a‖ = ‖f a'‖ := by rw [hflat a ha, hflat a' ha']
    have hps1 : ps a * ps (-a) = 1 := by
      rw [← AddChar.map_add_eq_mul]; simp
    have hsplit : ps (a - a') = ps a * ps (-a') := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      abel
    calc f a = (ps a * ps (-a)) * f a := by rw [hps1, one_mul]
      _ = ps a * (ps (-a) * f a) := by ring
      _ = ps a * ((‖f a‖ : ℂ) * (gdft f ps / ((‖gdft f ps‖ : ℝ) : ℂ))) := by
          rw [hphase ps hps a]
      _ = ps a * ((‖f a'‖ : ℂ) * (gdft f ps / ((‖gdft f ps‖ : ℝ) : ℂ))) := by rw [hflateq]
      _ = ps a * (ps (-a') * f a') := by rw [← hphase ps hps a']
      _ = (ps a * ps (-a')) * f a' := by ring
      _ = ps (a - a') * f a' := by rw [hsplit]
  have hsuppne : ∀ x ∈ gsupport f, f x ≠ 0 := by
    intro x hx
    simp only [gsupport, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact hx
  have horth : ∀ ps ∈ dsupport (gdft f), ∀ qs ∈ dsupport (gdft f),
      ∀ a ∈ gsupport f, ∀ a' ∈ gsupport f, ps (a - a') = qs (a - a') := by
    intro ps hps qs hqs a ha a' ha'
    have h1 := hchar ps hps a ha a' ha'
    have h2 := hchar qs hqs a ha a' ha'
    exact mul_right_cancel₀ (hsuppne a' ha') (by rw [← h1, ← h2])
  -- base point and base character
  have hGpos2 : 0 < Fintype.card G := Fintype.card_pos
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, a₀ ∈ gsupport f := by
    rcases Finset.eq_empty_or_nonempty (gsupport f) with he | hne
    · exfalso
      have hz : (gsupport f).card = 0 := by rw [he]; simp
      rw [hz, zero_mul] at hext
      omega
    · exact hne
  obtain ⟨psi₀, hpsi₀⟩ : ∃ p, p ∈ dsupport (gdft f) := by
    rcases Finset.eq_empty_or_nonempty (dsupport (gdft f)) with he | hne
    · exfalso
      have hz : (dsupport (gdft f)).card = 0 := by rw [he]; simp
      rw [hz, mul_zero] at hext
      omega
    · exact hne
  set K : Finset G := (gsupport f).image (fun a => a - a₀) with hKdef
  have hKmem : ∀ x : G, x ∈ K ↔ x + a₀ ∈ gsupport f := by
    intro x
    rw [hKdef, Finset.mem_image]
    constructor
    · rintro ⟨b, hb, rfl⟩
      simpa using hb
    · intro h
      exact ⟨x + a₀, h, by abel⟩
  have hKinj : Function.Injective (fun a : G => a - a₀) := fun x y hxy => by
    simpa using hxy
  have hKcard : K.card = (gsupport f).card := Finset.card_image_of_injective _ hKinj
  have hK0 : (0 : G) ∈ K := by
    rw [hKmem]
    simpa using ha₀
  -- the annihilator of `K` in the dual group
  set A : Finset (AddChar G ℂ) := annChar K with hAdef
  have hAmem : ∀ ps : AddChar G ℂ, ps ∈ A ↔ ∀ b ∈ K, ps b = 1 := by
    intro ps
    rw [hAdef, annChar, Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩
  have hAone : (1 : AddChar G ℂ) ∈ A := (hAmem 1).2 (fun b _ => rfl)
  have hAmul : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ A := by
    intro x hx y hy
    refine (hAmem _).2 (fun b hb => ?_)
    rw [AddChar.mul_apply, (hAmem x).1 hx b hb, (hAmem y).1 hy b hb, one_mul]
  -- duality counting for the subgroup `A`
  have hdual : (annGrp A).card * A.card = Fintype.card G := by
    -- the double character sum, summed with the character outside
    have houter : ∑ ps ∈ A, ∑ x : G, ps x = (Fintype.card G : ℂ) := by
      rw [Finset.sum_eq_single (1 : AddChar G ℂ)]
      · simp
      · intro ps hps hne
        exact AddChar.sum_eq_zero_iff_ne_zero.2 (by simpa using hne)
      · intro h; exact absurd hAone h
    -- the inner sum over a subgroup is `|A|` on the annihilator and `0` off it
    have hinner : ∀ x : G, ∑ ps ∈ A, ps x = if x ∈ annGrp A then (A.card : ℂ) else 0 := by
      intro x
      by_cases hx : x ∈ annGrp A
      · rw [if_pos hx]
        have hall : ∀ ps ∈ A, ps x = 1 := by
          intro ps hps
          rw [annGrp, Finset.mem_filter] at hx
          exact hx.2 ps hps
        rw [Finset.sum_congr rfl hall, Finset.sum_const, nsmul_eq_mul, mul_one]
      · rw [if_neg hx]
        obtain ⟨phi, hphiA, hphi⟩ : ∃ phi ∈ A, phi x ≠ 1 := by
          by_contra hc
          push_neg at hc
          exact hx (by rw [annGrp, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hc⟩)
        -- translating by `phi` permutes `A`
        have hinj : Function.Injective (fun ps : AddChar G ℂ => phi * ps) := by
          intro p q hpq
          exact mul_left_cancel hpq
        have hsubimg : A.image (fun ps => phi * ps) ⊆ A := by
          intro y hy
          rw [Finset.mem_image] at hy
          obtain ⟨p, hp, rfl⟩ := hy
          exact hAmul phi hphiA p hp
        have hcardimg : (A.image (fun ps => phi * ps)).card = A.card :=
          Finset.card_image_of_injective A hinj
        have himg : A.image (fun ps => phi * ps) = A :=
          Finset.eq_of_subset_of_card_le hsubimg (le_of_eq hcardimg.symm)
        have hshift : ∑ ps ∈ A, ps x = phi x * ∑ ps ∈ A, ps x := by
          calc ∑ ps ∈ A, ps x
              = ∑ ps ∈ A.image (fun p => phi * p), ps x := by rw [himg]
            _ = ∑ ps ∈ A, (phi * ps) x := Finset.sum_image (fun p _ q _ h => hinj h)
            _ = ∑ ps ∈ A, phi x * ps x := by
                refine Finset.sum_congr rfl (fun p _ => ?_)
                rw [AddChar.mul_apply]
            _ = phi x * ∑ ps ∈ A, ps x := by rw [Finset.mul_sum]
        have hsub : (phi x - 1) * ∑ ps ∈ A, ps x = 0 := by
          rw [sub_mul, one_mul, ← hshift]
          ring
        rcases mul_eq_zero.1 hsub with h | h
        · exact absurd (by linear_combination h) hphi
        · exact h
    -- compare the two orders of summation
    have hswap : ∑ ps ∈ A, ∑ x : G, ps x = ∑ x : G, ∑ ps ∈ A, ps x := Finset.sum_comm
    rw [hswap, Finset.sum_congr rfl (fun x _ => hinner x)] at houter
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul] at houter
    exact_mod_cast houter
  -- `K` sits inside the annihilator of `A`
  have hKsub : K ⊆ annGrp A := by
    intro x hx
    rw [annGrp, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun ps hps => (hAmem ps).1 hps x hx⟩
  -- the translated spectrum sits inside `A`
  have hcharne : ∀ (ps : AddChar G ℂ) (x : G), ps x ≠ 0 := by
    intro ps x hz
    have hone : ps x * ps (-x) = 1 := by
      rw [← AddChar.map_add_eq_mul]; simp
    rw [hz, zero_mul] at hone
    exact zero_ne_one hone
  have hHsub : ∀ ps ∈ dsupport (gdft f), psi₀⁻¹ * ps ∈ A := by
    intro ps hps
    refine (hAmem _).2 (fun b hb => ?_)
    have hb' : b + a₀ ∈ gsupport f := (hKmem b).1 hb
    have hbe : b = (b + a₀) - a₀ := by abel
    have heq : ps b = psi₀ b := by
      rw [hbe]
      exact horth ps hps psi₀ hpsi₀ (b + a₀) hb' a₀ ha₀
    rw [AddChar.mul_apply, AddChar.inv_apply', heq]
    exact inv_mul_cancel₀ (hcharne psi₀ b)
  have hHinj : Function.Injective (fun ps : AddChar G ℂ => psi₀⁻¹ * ps) :=
    fun p q hpq => mul_left_cancel hpq
  set H : Finset (AddChar G ℂ) := (dsupport (gdft f)).image (fun ps => psi₀⁻¹ * ps) with hHdef
  have hHcard : H.card = (dsupport (gdft f)).card := Finset.card_image_of_injective _ hHinj
  have hHA : H ⊆ A := by
    intro y hy
    rw [hHdef, Finset.mem_image] at hy
    obtain ⟨p, hp, rfl⟩ := hy
    exact hHsub p hp
  -- the cardinality squeeze pins both annihilators
  have hAge : (dsupport (gdft f)).card ≤ A.card := by
    rw [← hHcard]
    exact Finset.card_le_card hHA
  have hKge : (gsupport f).card ≤ (annGrp A).card := by
    rw [← hKcard]
    exact Finset.card_le_card hKsub
  have hAnnEq : (annGrp A).card = (gsupport f).card := by
    have h1 : (gsupport f).card * (dsupport (gdft f)).card ≤ (annGrp A).card * A.card :=
      Nat.mul_le_mul hKge hAge
    have h2 : (annGrp A).card * A.card = (gsupport f).card * (dsupport (gdft f)).card := by
      rw [hdual, ← hext]
    nlinarith [hKge, hAge, h1, h2]
  have hKeq : K = annGrp A := by
    refine Finset.eq_of_subset_of_card_le hKsub ?_
    rw [hKcard, hAnnEq]
  -- hence `K` is a subgroup
  have hKadd : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K := by
    intro x hx y hy
    rw [hKeq] at hx hy ⊢
    rw [annGrp, Finset.mem_filter] at hx hy ⊢
    refine ⟨Finset.mem_univ _, fun ps hps => ?_⟩
    rw [AddChar.map_add_eq_mul, hx.2 ps hps, hy.2 ps hps, one_mul]
  -- the closed form
  refine ⟨K, a₀, psi₀, f a₀ * (psi₀ a₀)⁻¹, ?_, hK0, hKadd, hKcard, ?_⟩
  · exact mul_ne_zero (hsuppne a₀ ha₀) (inv_ne_zero (hcharne psi₀ a₀))
  · intro a
    have hiff : a - a₀ ∈ K ↔ a ∈ gsupport f := by
      rw [hKmem]
      constructor
      · intro h; simpa using h
      · intro h; simpa using h
    by_cases hmem : a ∈ gsupport f
    · rw [if_pos (hiff.2 hmem)]
      have hc := hchar psi₀ hpsi₀ a hmem a₀ ha₀
      have hsplit : psi₀ (a - a₀) = psi₀ a * (psi₀ a₀)⁻¹ := by
        rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv]
      rw [hc, hsplit]
      ring
    · rw [if_neg (fun h => hmem (hiff.1 h))]
      simp only [gsupport, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hmem
      exact hmem
