-- Prove2me | solution 1 for CouretOaiBridge01.NORM02.prime_center_label_unique
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:00:44.345764+00:00
-- url     : https://prove2.me/submissions/ca43d7f4-7ce9-4cad-902f-3927cdc1f12e

import Mathlib
import Mathlib

/-!
# NORM-02 — finite arithmetic certification layer

This file formalizes elementary, reusable sublemmas of NORM-01:
* exact coverage of the middle tent window by fixed anchor indices;
* primality and coprimality of those anchor indices;
* unique prime label for small-index centers;
* finite bad-square counting budget;
* the rational constant 3/50 in the mass lower bound.

Not formalized here: the 2026 Matomäki–Radziwill–Shao–Tao–Teräväinen
short-interval theorem, the asymptotic exceptional-set estimate, the full
squarefree sieve or the normalized Möbius correlation asymptotics.

RESEARCH ONLY. No sorry, no axioms added, no RH claim, no novelty claim.
-/

namespace CouretOaiBridge01
namespace NORM02









/-- A prime > P dividing one center cannot also divide its small index.
The proof uses only the prime-divides-a-product lemma. -/
theorem p2m_local_prime_center_label_unique
    (P p q m n : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpP : P < p) (hqP : P < q)
    (hm : 0 < m) (hn : 0 < n)
    (hmP : m < P) (hnP : n < P)
    (heq : p * m = q * n) :
    p = q := by
  have hpdvd : p ∣ q * n := by
    rw [← heq]
    exact ⟨m, rfl⟩
  have hqdvd : q ∣ p * m := by
    rw [heq]
    exact ⟨n, rfl⟩
  have hpnotn : ¬ p ∣ n := by
    intro h
    have hle := Nat.le_of_dvd hn h
    omega
  have hqnotm : ¬ q ∣ m := by
    intro h
    have hle := Nat.le_of_dvd hm h
    omega
  have hpq : p ∣ q := by
    rcases (Nat.Prime.dvd_mul hp).mp hpdvd with hpq | hpn
    · exact hpq
    · exact False.elim (hpnotn hpn)
  have hqp : q ∣ p := by
    rcases (Nat.Prime.dvd_mul hq).mp hqdvd with hqp | hqm
    · exact hqp
    · exact False.elim (hqnotm hqm)
  exact Nat.le_antisymm (Nat.le_of_dvd hq.pos hpq)
    (Nat.le_of_dvd hp.pos hqp)





end NORM02
end CouretOaiBridge01

theorem solution : ∀ (P p q m n : Nat),
  Nat.Prime p →
    Nat.Prime q →
      @LT.lt.{0} Nat instLTNat P p →
        @LT.lt.{0} Nat instLTNat P q →
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) m →
            @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
              @LT.lt.{0} Nat instLTNat m P →
                @LT.lt.{0} Nat instLTNat n P →
                  @Eq.{1} Nat (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) p m)
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) q n) →
                    @Eq.{1} Nat p q := @_root_.CouretOaiBridge01.NORM02.p2m_local_prime_center_label_unique

