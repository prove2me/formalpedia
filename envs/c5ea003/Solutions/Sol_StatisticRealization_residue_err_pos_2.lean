-- Prove2me | solution 2 for StatisticRealization.residue_err_pos
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T03:39:01.046178+00:00
-- url     : https://prove2.me/submissions/bb4e9867-1af5-43b8-be0e-27e6500ebdf2

import Mathlib
import Definitions.Def_Novelty_OracleRealizationGap
import Definitions.Def_Novelty_StatisticRealizationBound

open StatisticRealization OracleRealizationGap Finset in
theorem solution (L B : ℕ) (hL : L ≠ 0) :
    ∃ p q₁ q₂ : ℕ, p.Prime ∧ q₁.Prime ∧ q₂.Prime ∧ (p, q₁) ≠ (p, q₂) ∧
      ∀ f : ℕ → Bool,
        0 < err ({(p, q₁), (p, q₂)} : Finset (ℕ × ℕ))
          (fun x => (x.1 * x.2) % L) (fun x => sensor B x.1 x.2) f := by
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
  refine ⟨r, r, q, hr, hr, hq, ?_, fun f => ?_⟩
  · intro h
    have := (Prod.mk.inj h).2
    omega
  -- whatever `f` answers on the shared residue, it errs on one of the two products
  unfold err
  rw [Finset.card_pos]
  by_cases hv : f (r * r % L) = true
  · refine ⟨(r, q), Finset.mem_filter.2 ⟨by simp, ?_⟩⟩
    show f (r * q % L) ≠ sensor B r q
    rw [← heq, hv, hs2]
    decide
  · refine ⟨(r, r), Finset.mem_filter.2 ⟨by simp, ?_⟩⟩
    show f (r * r % L) ≠ sensor B r r
    rw [hs1]
    exact hv
