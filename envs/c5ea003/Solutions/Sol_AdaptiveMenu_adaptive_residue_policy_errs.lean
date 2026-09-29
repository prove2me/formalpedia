-- Prove2me | solution 1 for AdaptiveMenu.adaptive_residue_policy_errs
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T22:35:51.427893+00:00
-- url     : https://prove2.me/submissions/64ddc107-43df-4ef5-ba0a-44a074ddc83c

import Mathlib
import Definitions.Def_Novelty_AdaptiveMenuCapacity
import Definitions.Def_Novelty_OracleRealizationGap
import Definitions.Def_Novelty_StatisticRealizationBound

open AdaptiveMenu QueryTree OracleRealizationGap in
theorem solution (L B : ℕ) (hL : L ≠ 0) :
    ∃ p q₁ q₂ : ℕ, p.Prime ∧ q₁.Prime ∧ q₂.Prime ∧ q₁ ≠ q₂ ∧
      ∀ t : QueryTree (ℕ × ℕ), t.Uses (residueMenu L) →
        t.eval (p, q₁) ≠ sensor B p q₁ ∨ t.eval (p, q₂) ≠ sensor B p q₂ := by
  -- a tree of residue queries cannot separate two samples with the same residue
  have hres : ∀ t : QueryTree (ℕ × ℕ), t.Uses (residueMenu L) → ∀ x y : ℕ × ℕ,
      x.1 * x.2 % L = y.1 * y.2 % L → t.eval x = t.eval y := by
    intro t
    induction t with
    | leaf b =>
      intro _ x y _
      rfl
    | node m t f iht ihf =>
      intro hu x y hxy
      obtain ⟨hm, hut, huf⟩ := hu
      obtain ⟨r0, rfl⟩ := hm
      simp only [eval]
      simp only [hxy, iht hut x y hxy, ihf huf x y hxy]
  -- an odd prime `r > L`, and (Dirichlet) a prime `q ≡ r (mod L)` far beyond `r` and `B`
  obtain ⟨r, hrL, hr⟩ := Nat.exists_infinite_primes (L + 3)
  have hr2 : r ≠ 2 := by omega
  have hcop : r.Coprime L :=
    (Nat.Prime.coprime_iff_not_dvd hr).2
      (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hL) (by omega))
  haveI : NeZero L := ⟨hL⟩
  have hunit : IsUnit (r : ZMod L) := (ZMod.isUnit_iff_coprime r L).2 hcop
  obtain ⟨q, hqM, hq, hqr⟩ := Nat.forall_exists_prime_gt_and_eq_mod hunit (4 * (B + r + 2))
  have hmodq : q ≡ r [MOD L] := (ZMod.natCast_eq_natCast_iff q r L).1 hqr
  have heq : r * r % L = r * q % L := hmodq.symm.mul_left r
  have hgap0 : gap r r = 0 := by
    unfold gap mid
    rw [Nat.sqrt_eq]
    omega
  have hgapq : B < gap r q := by
    have hs : Nat.sqrt (r * q) ≤ q / 4 + r := by
      set t := q / 4 with ht
      have h4 : q < 4 * t + 4 := by omega
      have h5 : r * q < r * (4 * t + 4) := by nlinarith [hr.pos]
      have h6 : r * (4 * t + 4) ≤ (t + r + 1) ^ 2 := by
        zify
        nlinarith [sq_nonneg ((t : ℤ) - r + 1)]
      have hlt : r * q < (t + r + 1) ^ 2 := by omega
      exact Nat.lt_succ_iff.1 (Nat.sqrt_lt'.2 hlt)
    unfold gap mid
    omega
  have hs1 : sensor B r r = true := by simp [sensor, hgap0]
  have hs2 : sensor B r q = false := by
    simp only [sensor, decide_eq_false_iff_not, not_le]
    exact hgapq
  refine ⟨r, r, q, hr, hr, hq, by omega, fun t ht => ?_⟩
  by_contra hcon
  rw [not_or, not_ne_iff, not_ne_iff] at hcon
  obtain ⟨h1, h2⟩ := hcon
  have h3 := hres t ht (r, r) (r, q) heq
  rw [h1, h2, hs1, hs2] at h3
  exact Bool.noConfusion h3
