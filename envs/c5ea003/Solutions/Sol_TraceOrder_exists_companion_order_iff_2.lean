-- Prove2me | solution 2 for TraceOrder.exists_companion_order_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T17:31:47.405811+00:00
-- url     : https://prove2.me/submissions/b702973d-309a-4866-823f-eab64dd990b1

import Mathlib
import Definitions.Def_Applications_CyclicCubicTypeChannel_TraceOrder

open TraceOrder in
theorem solution (p : ℕ) [hp : Fact p.Prime] {m : ℕ} (hm : m.Prime) (hm2 : m ≠ 2)
    (hmp : m ≠ p) :
    (∃ t : ZMod p, comp (ZMod p) t ^ m = 1 ∧ comp (ZMod p) t ≠ 1) ↔ m ∣ p ^ 2 - 1 := by
  classical
  have hp1 : 1 < p := hp.out.one_lt
  have hm3 : 3 ≤ m := by have := hm.two_le; omega
  have hm1 : 1 ≤ m := by omega
  -- `p² − 1 = (p − 1)(p + 1)`
  have hfactor : p ^ 2 - 1 = (p - 1) * (p + 1) := by
    obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    have h1 : (q + 1) ^ 2 = q * (q + 2) + 1 := by ring
    rw [hq, h1, Nat.add_sub_cancel, Nat.add_sub_cancel]
  -- the companion matrix satisfies `M² = tM − 1`
  have hMsq : ∀ t : ZMod p, comp (ZMod p) t ^ 2 = t • comp (ZMod p) t - 1 := by
    intro t
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [comp, sq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring
  -- powers of the companion matrix via the Chebyshev coefficients
  have hMpow : ∀ (t : ZMod p) (n : ℕ),
      comp (ZMod p) t ^ (n + 1) = chebA t (n + 1) • comp (ZMod p) t - chebA t n • 1 := by
    intro t n
    induction n with
    | zero => simp [chebA]
    | succ k ih =>
      show comp (ZMod p) t ^ (k + 2) = chebA t (k + 2) • comp (ZMod p) t - chebA t (k + 1) • 1
      have hrec : chebA t (k + 2) = chebA t (k + 1) * t - chebA t k := by
        rw [chebA.eq_3]; ring
      rw [hrec, pow_succ, ih, sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul, ← pow_two,
        hMsq, smul_sub, smul_smul, sub_smul]
      abel
  -- powers of a root of `Y² − τY + 1`
  have hzpow : ∀ {F : Type} [Field F] (τ ζ : F), ζ ^ 2 - τ * ζ + 1 = 0 →
      ∀ n : ℕ, ζ ^ (n + 1) = chebA τ (n + 1) * ζ - chebA τ n := by
    intro F _ τ ζ hq n
    induction n with
    | zero => simp [chebA]
    | succ k ih =>
      show ζ ^ (k + 2) = chebA τ (k + 2) * ζ - chebA τ (k + 1)
      rw [chebA.eq_3]
      linear_combination ζ * ih + chebA τ (k + 1) * hq
  -- ring homomorphisms commute with the Chebyshev coefficients
  have hmapcheb : ∀ {F : Type} [Field F] (φ : ZMod p →+* F) (t : ZMod p) (n : ℕ),
      φ (chebA t n) = chebA (φ t) n := by
    intro F _ φ t n
    have key : ∀ n, φ (chebA t n) = chebA (φ t) n ∧
        φ (chebA t (n + 1)) = chebA (φ t) (n + 1) := by
      intro n
      induction n with
      | zero => exact ⟨by simp [chebA], by simp [chebA]⟩
      | succ k ih =>
        refine ⟨ih.2, ?_⟩
        show φ (chebA t (k + 2)) = chebA (φ t) (k + 2)
        rw [chebA.eq_3, chebA.eq_3, map_sub, map_mul, ih.1, ih.2]
    exact (key n).1
  -- `chebA 2 n = n`
  have hcheb2 : ∀ n : ℕ, chebA (2 : ZMod p) n = n ∧ chebA (2 : ZMod p) (n + 1) = n + 1 := by
    intro n
    induction n with
    | zero => exact ⟨by simp [chebA], by simp [chebA]⟩
    | succ k ih =>
      refine ⟨by rw [ih.2]; push_cast; ring, ?_⟩
      show chebA (2 : ZMod p) (k + 2) = ((k + 1 : ℕ) : ZMod p) + 1
      rw [chebA.eq_3, ih.1, ih.2]
      push_cast
      ring
  -- in a field of characteristic `p`, an element `ζ ≠ 1` with `ζ ^ m = 1` that is a root of
  -- `Y² − τY + 1` with `τ ^ p = τ` forces `m ∣ p² − 1`
  have hfrob : ∀ {F : Type} [Field F] [CharP F p] (τ ζ : F), τ ^ p = τ →
      ζ ^ 2 - τ * ζ + 1 = 0 → ζ ^ m = 1 → ζ ≠ 1 → m ∣ p ^ 2 - 1 := by
    intro F _ _ τ ζ hτp hq hζm hζ1
    have hζ0 : ζ ≠ 0 := by
      intro h
      rw [h] at hq
      norm_num at hq
    have hdvd : ∀ n : ℕ, ζ ^ n = 1 → m ∣ n := by
      intro n hn
      by_contra hnd
      have hcop : Nat.Coprime n m := Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hm).2 hnd)
      have h := (pow_gcd_eq_one (a := ζ) (m := n) (n := m)).2 ⟨hn, hζm⟩
      rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h
      exact hζ1 h
    have hquadp : (ζ ^ p) ^ 2 - τ * ζ ^ p + 1 = 0 := by
      have h : (ζ ^ 2 - τ * ζ + 1) ^ p = 0 := by
        rw [hq, zero_pow hp.out.ne_zero]
      rw [add_pow_char, sub_pow_char, mul_pow, one_pow, hτp] at h
      linear_combination h
    have hfac : (ζ ^ p - ζ) * (ζ ^ p - (τ - ζ)) = 0 := by
      linear_combination hquadp - hq
    obtain ⟨q, hq'⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    rw [hfactor]
    rcases mul_eq_zero.1 hfac with hA | hB
    · have hpq : ζ ^ p = ζ ^ (q + 1) := congrArg (ζ ^ ·) hq'
      have hq1 : ζ * (ζ ^ q - 1) = 0 := by
        linear_combination hA - hpq
      have hzq : ζ ^ q = 1 := sub_eq_zero.1 ((mul_eq_zero.1 hq1).resolve_left hζ0)
      have h := hdvd q hzq
      have : p - 1 = q := by omega
      rw [this]
      exact Dvd.dvd.mul_right h _
    · have hzp : ζ ^ (p + 1) = 1 := by
        linear_combination ζ * hB - hq
      exact Dvd.dvd.mul_left (hdvd (p + 1) hzp) _
  constructor
  · rintro ⟨t, hMm, -⟩
    obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hform := hMpow t k
    rw [← hk, hMm] at hform
    have ha : chebA t m = 0 := by
      have h := congrFun (congrFun hform 0) 1
      simp [comp, Matrix.one_apply] at h
      first
        | exact h
        | exact h.symm
        | linear_combination h
        | linear_combination -h
    have hb : chebA t k = -1 := by
      have h := congrFun (congrFun hform 1) 1
      simp [comp, Matrix.one_apply] at h
      first
        | exact h
        | exact h.symm
        | linear_combination h
        | linear_combination -h
        | linear_combination -h.symm
        | (rw [ha] at h; linear_combination -h)
        | (rw [ha] at h; linear_combination h)
    -- a root of `Y² − tY + 1` in the algebraic closure
    let L := AlgebraicClosure (ZMod p)
    haveI : CharP L p := charP_of_injective_algebraMap (algebraMap (ZMod p) L).injective p
    obtain ⟨τ, hτ⟩ : ∃ τ : L, τ = algebraMap (ZMod p) L t := ⟨_, rfl⟩
    have hdeg : (Polynomial.X ^ 2 - Polynomial.C τ * Polynomial.X + 1 :
        Polynomial L).degree = 2 := by
      compute_degree!
    obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root
      (Polynomial.X ^ 2 - Polynomial.C τ * Polynomial.X + 1 : Polynomial L)
      (by rw [hdeg]; decide)
    have hq : ζ ^ 2 - τ * ζ + 1 = 0 := by
      have h := hζ
      simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        Polynomial.eval_one] at h
      exact h
    have hζm : ζ ^ m = 1 := by
      have h := hzpow τ ζ hq k
      rw [← hk] at h
      rw [h, hτ, ← hmapcheb, ← hmapcheb, ha, hb, map_zero, map_neg, map_one]
      ring
    have hζ1 : ζ ≠ 1 := by
      intro h1
      have hτ2 : τ = 2 := by
        rw [h1] at hq
        linear_combination -hq
      have ht2 : t = 2 := by
        apply (algebraMap (ZMod p) L).injective
        rw [← hτ, hτ2, map_ofNat]
      rw [ht2, (hcheb2 m).1] at ha
      have hpm : p ∣ m := (CharP.cast_eq_zero_iff (ZMod p) p m).1 ha
      exact hmp ((Nat.prime_dvd_prime_iff_eq hp.out hm).1 hpm).symm
    have hτp : τ ^ p = τ := by
      rw [hτ, ← map_pow, ZMod.pow_card]
    exact hfrob τ ζ hτp hq hζm hζ1
  · intro hdiv
    let K := GaloisField p 2
    letI : Fintype K := Fintype.ofFinite K
    have hcardK : Fintype.card K = p ^ 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact GaloisField.card p 2 (by norm_num)
    haveI : Fact m.Prime := ⟨hm⟩
    have hmK : m ∣ Fintype.card Kˣ := by
      rw [Fintype.card_units, hcardK]
      exact hdiv
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card m hmK
    obtain ⟨ζ, hζdef⟩ : ∃ ζ : K, ζ = (g : K) := ⟨_, rfl⟩
    have hζm : ζ ^ m = 1 := by
      have h := pow_orderOf_eq_one g
      rw [hg] at h
      have := congrArg Units.val h
      simpa [hζdef] using this
    have hζ0 : ζ ≠ 0 := by
      rw [hζdef]
      exact Units.ne_zero g
    have hdvd : ∀ n : ℕ, ζ ^ n = 1 → m ∣ n := by
      intro n hn
      have hgn : g ^ n = 1 := by
        apply Units.val_eq_one.1
        rw [Units.val_pow_eq_pow_val, ← hζdef, hn]
      rw [← hg]
      exact orderOf_dvd_of_pow_eq_one hgn
    have hζinv : ζ * ζ ^ (m - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hm1, hζm]
    obtain ⟨z, hzdef⟩ : ∃ z : K, z = ζ ^ (m - 1) := ⟨_, rfl⟩
    rw [← hzdef] at hζinv
    have hzm : z ^ m = 1 := by
      rw [hzdef, ← pow_mul, mul_comm, pow_mul, hζm, one_pow]
    have hζz : ζ ≠ z := by
      intro h
      have h2 : ζ ^ 2 = 1 := by
        rw [sq]
        nth_rewrite 2 [h]
        exact hζinv
      have := Nat.le_of_dvd (by norm_num) (hdvd 2 h2)
      omega
    obtain ⟨η, hηdef⟩ : ∃ η : K, η = ζ + z := ⟨_, rfl⟩
    have hpm : m ∣ p - 1 ∨ m ∣ p + 1 := by
      rw [hfactor] at hdiv
      exact (Nat.Prime.dvd_mul hm).1 hdiv
    have hηfix : η ^ p = η := by
      have hfr : η ^ p = ζ ^ p + z ^ p := by
        rw [hηdef, add_pow_char]
      have hinvp : ζ ^ p * z ^ p = 1 := by
        rw [← mul_pow, hζinv, one_pow]
      rw [hfr, hηdef]
      rcases hpm with h | h
      · obtain ⟨c, hc⟩ := h
        have hp1' : ζ ^ (p - 1) = 1 := by
          rw [hc, pow_mul, hζm, one_pow]
        have hsplit : ζ ^ p = ζ ^ (p - 1) * ζ := by
          rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le]
        have hζp : ζ ^ p = ζ := by
          rw [hsplit, hp1', one_mul]
        have hzp : z ^ p = z := by
          linear_combination (-z ^ p) * hζinv + z * hinvp - z * z ^ p * hζp
        rw [hζp, hzp]
      · obtain ⟨c, hc⟩ := h
        have hp1' : ζ ^ (p + 1) = 1 := by
          rw [hc, pow_mul, hζm, one_pow]
        have hζp : ζ ^ p = z := by
          linear_combination z * hp1' - ζ ^ p * hζinv
        have hzp : z ^ p = ζ := by
          linear_combination (-z ^ p) * hζinv + ζ * hinvp - ζ * z ^ p * hζp
        rw [hζp, hzp, add_comm]
    -- elements fixed by Frobenius lie in the prime field
    have hmem : ∃ r : ZMod p, algebraMap (ZMod p) K r = η := by
      by_contra hnot
      simp only [not_exists] at hnot
      have hP0 := FiniteField.X_pow_card_sub_X_ne_zero K hp1
      have hPdeg := FiniteField.X_pow_card_sub_X_natDegree_eq K hp1
      have hS : insert η (Finset.univ.image (algebraMap (ZMod p) K)) ⊆
          (Polynomial.X ^ p - Polynomial.X : Polynomial K).roots.toFinset := by
        intro s hs
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot,
          Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
        rcases Finset.mem_insert.1 hs with rfl | hs
        · rw [hηfix, sub_self]
        · obtain ⟨r, -, rfl⟩ := Finset.mem_image.1 hs
          rw [← map_pow, ZMod.pow_card, sub_self]
      have hηnot : η ∉ Finset.univ.image (algebraMap (ZMod p) K) := by
        intro h
        obtain ⟨r, -, hr⟩ := Finset.mem_image.1 h
        exact hnot r hr
      have hcard : (insert η (Finset.univ.image (algebraMap (ZMod p) K))).card = p + 1 := by
        rw [Finset.card_insert_of_notMem hηnot,
          Finset.card_image_of_injective _ (algebraMap (ZMod p) K).injective,
          Finset.card_univ, ZMod.card]
      have hle := ((Finset.card_le_card hS).trans (Multiset.toFinset_card_le _)).trans
        (Polynomial.card_roots' (Polynomial.X ^ p - Polynomial.X : Polynomial K))
      rw [hcard, hPdeg] at hle
      omega
    obtain ⟨r, hr⟩ := hmem
    refine ⟨r, ?_, ?_⟩
    · -- both `ζ` and `z = ζ⁻¹` are roots of `Y² − ηY + 1`
      have hqζ : ζ ^ 2 - η * ζ + 1 = 0 := by
        rw [hηdef]
        linear_combination -hζinv
      have hqz : z ^ 2 - η * z + 1 = 0 := by
        rw [hηdef]
        linear_combination -hζinv
      have h1 := hzpow η ζ hqζ (m - 1)
      have h2 := hzpow η z hqz (m - 1)
      rw [Nat.sub_add_cancel hm1, hζm] at h1
      rw [Nat.sub_add_cancel hm1, hzm] at h2
      have hA : chebA η m = 0 := by
        have h : chebA η m * (ζ - z) = 0 := by
          linear_combination h2 - h1
        exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hζz)
      have hB : chebA η (m - 1) = -1 := by
        rw [hA] at h1
        linear_combination h1
      have hA' : chebA r m = 0 := by
        apply (algebraMap (ZMod p) K).injective
        rw [hmapcheb, hr, hA, map_zero]
      have hB' : chebA r (m - 1) = -1 := by
        apply (algebraMap (ZMod p) K).injective
        rw [hmapcheb, hr, hB, map_neg, map_one]
      have h := hMpow r (m - 1)
      rw [Nat.sub_add_cancel hm1] at h
      rw [h, hA', hB']
      simp
    · intro h
      have h01 := congrFun (congrFun h 0) 1
      simp [comp] at h01
