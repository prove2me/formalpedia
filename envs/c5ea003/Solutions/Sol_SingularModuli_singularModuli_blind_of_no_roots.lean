-- Prove2me | solution 1 for SingularModuli.singularModuli_blind_of_no_roots
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T22:52:25.521017+00:00
-- url     : https://prove2.me/submissions/34f9b28c-3056-43fd-ab28-57aa1f30dc73

import Mathlib
import Definitions.Def_Cryptography_FactoringBarriers_CongruenceOfSquares
import Definitions.Def_Cryptography_SingularModuli_GcdCriterion

/-!
# Singular Moduli Factoring, Step 1: the exact gcd criterion

The failure mode of the single-step test: if `H` has no root modulo either prime
`p` or `q`, then every evaluation point `x` is useless — the gcd is never a
nontrivial divisor of `p*q`.
-/

open SingularModuli

open Polynomial FactoringBarriers

variable {p q : ℕ} {H : Polynomial ℤ} {j : ℤ}

namespace SingularModuli

theorem solution (hp : p.Prime) (hq : q.Prime)
    (hpd : ∀ x : ℤ, ¬ (p : ℤ) ∣ H.eval x) (hqd : ∀ x : ℤ, ¬ (q : ℤ) ∣ H.eval x) :
    ∀ x : ℤ, ¬ NontrivialDivisor (p * q) (evalGcd H x (p * q)) := by
  intro x hntr
  obtain ⟨hdvd, h1lt, -⟩ := hntr
  obtain ⟨r, hrp, hrd⟩ :=
    Nat.exists_prime_and_dvd (n := evalGcd H x (p * q)) (by omega)
  have hrdvd_a : (r : ℤ) ∣ H.eval x :=
    dvd_trans (Int.natCast_dvd_natCast.mpr hrd)
      (Int.gcd_dvd_left (H.eval x) ((p * q : ℕ) : ℤ))
  have hr_dvd_pq : r ∣ p * q := dvd_trans hrd hdvd
  rcases (hrp.dvd_mul.mp hr_dvd_pq) with hrp' | hrq'
  · have hr_eq : r = p := ((Nat.dvd_prime hp).mp hrp').resolve_left hrp.ne_one
    exact hpd x (hr_eq ▸ hrdvd_a)
  · have hr_eq : r = q := ((Nat.dvd_prime hq).mp hrq').resolve_left hrp.ne_one
    exact hqd x (hr_eq ▸ hrdvd_a)

end SingularModuli

open SingularModuli

theorem solution (hp : p.Prime) (hq : q.Prime)
    (hpd : ∀ x : ℤ, ¬ (p : ℤ) ∣ H.eval x) (hqd : ∀ x : ℤ, ¬ (q : ℤ) ∣ H.eval x) :
    ∀ x : ℤ, ¬ NontrivialDivisor (p * q) (evalGcd H x (p * q)) :=
  SingularModuli.solution hp hq hpd hqd

#print axioms solution
