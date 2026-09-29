-- Prove2me | solution 1 for AbelianCosetClassification.phase_of_extremal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-21T02:15:34.058307+00:00
-- url     : https://prove2.me/submissions/86efeca1-40bd-42fa-a484-d75c27766289

import Mathlib
import Definitions.Def_Bridges_AbelianCosetClassification
import Definitions.Def_Bridges_CosetClassification
import Definitions.Def_Bridges_FiniteAbelianUncertainty

set_option maxHeartbeats 1000000 in
open Finset FiniteAbelianUncertainty in
theorem solution {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    {f : G → ℂ} (hf : f ≠ 0)
    (hext : (gsupport f).card * (dsupport (gdft f)).card = Fintype.card G)
    {psi : AddChar G ℂ} (hpsi : psi ∈ dsupport (gdft f)) :
    ∀ a ∈ gsupport f,
      psi (-a) * f a = (‖f a‖ : ℂ) * (gdft f psi / (‖gdft f psi‖ : ℂ)) := by
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
  have hL1eq : ‖gdft f psi‖ = L1 := by
    have h2 := heach psi hpsi
    nlinarith [norm_nonneg (gdft f psi), hL1nn, h2]
  -- the Fourier coefficient is nonzero, so the unit phase is defined
  have hSne : gdft f psi ≠ 0 := by
    simp only [dsupport, Finset.mem_filter, Finset.mem_univ, true_and] at hpsi
    exact hpsi
  have hSpos : 0 < ‖gdft f psi‖ := norm_pos_iff.2 hSne
  set u : ℂ := gdft f psi / ((‖gdft f psi‖ : ℝ) : ℂ) with hudef
  have hcastne : ((‖gdft f psi‖ : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt hSpos
  -- `conj u * S` is the real number `‖S‖`
  have hkeyS : (starRingEnd ℂ) u * gdft f psi = ((‖gdft f psi‖ : ℝ) : ℂ) := by
    rw [hudef, map_div₀, Complex.conj_ofReal]
    field_simp
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  -- the terms of the sum, and the equality in the triangle inequality
  have hsumterm : ∑ a, ((starRingEnd ℂ) u * (psi (-a) * f a)).re = ‖gdft f psi‖ := by
    have h1 : ∑ a, ((starRingEnd ℂ) u * (psi (-a) * f a))
        = (starRingEnd ℂ) u * gdft f psi := by
      rw [gdft, Finset.mul_sum]
    have h2 : (∑ a, ((starRingEnd ℂ) u * (psi (-a) * f a))).re = ‖gdft f psi‖ := by
      rw [h1, hkeyS]; simp
    rw [← h2, Complex.re_sum]
  have hle : ∀ a : G, ((starRingEnd ℂ) u * (psi (-a) * f a)).re ≤ ‖f a‖ := by
    intro a
    have h1 := Complex.re_le_norm ((starRingEnd ℂ) u * (psi (-a) * f a))
    have hun : ‖(starRingEnd ℂ) u‖ = 1 := by
      rw [RCLike.norm_conj, hudef, norm_div, Complex.norm_real, norm_norm,
        div_self (ne_of_gt hSpos)]
    rw [norm_mul, hun, one_mul, norm_mul, hnorm1, one_mul] at h1
    exact h1
  have hzero : ∀ a : G, ((starRingEnd ℂ) u * (psi (-a) * f a)).re = ‖f a‖ := by
    intro a
    by_contra hne
    have hlt : ((starRingEnd ℂ) u * (psi (-a) * f a)).re < ‖f a‖ :=
      lt_of_le_of_ne (hle a) hne
    have hstrict : ∑ b, ((starRingEnd ℂ) u * (psi (-b) * f b)).re < ∑ b, ‖f b‖ :=
      Finset.sum_lt_sum (fun b _ => hle b) ⟨a, Finset.mem_univ a, hlt⟩
    rw [hsumterm, hL1eq, ← hL1def] at hstrict
    exact absurd rfl (ne_of_lt hstrict)
  -- a complex number whose real part equals its modulus is that nonnegative real
  intro a _
  have hw : (starRingEnd ℂ) u * (psi (-a) * f a) = ((‖f a‖ : ℝ) : ℂ) := by
    set w : ℂ := (starRingEnd ℂ) u * (psi (-a) * f a) with hwdef
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
  calc psi (-a) * f a = (u * (starRingEnd ℂ) u) * (psi (-a) * f a) := by rw [huu, one_mul]
    _ = u * ((starRingEnd ℂ) u * (psi (-a) * f a)) := by ring
    _ = u * ((‖f a‖ : ℝ) : ℂ) := by rw [hw]
    _ = ((‖f a‖ : ℝ) : ℂ) * (gdft f psi / ((‖gdft f psi‖ : ℝ) : ℂ)) := by rw [hudef]; ring
