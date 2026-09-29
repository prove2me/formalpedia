-- Prove2me | solution 1 for fib_quotient_gcd_dvd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T02:19:09.139737+00:00
-- url     : https://prove2.me/submissions/c67aeb36-28c6-413a-afb0-f6e3c8c5aefd

-- Sol generated from Shared/NumberTheory/CarmichaelHelpers.lean
import Mathlib
/-
# Helper Lemmas for Carmichael's Theorem

Key algebraic and divisibility properties of Fibonacci quotients.
-/

open Nat

set_option maxHeartbeats 4000000

/-! ## Basic Fibonacci growth -/

/-
F_n > 1 for n ≥ 3.
-/

/-
F_{km} > F_m for k ≥ 2 and m ≥ 2.
-/

/-! ## Fibonacci coprime product divisibility -/


/-! ## Fibonacci quotient GCD bound -/

/-
For m ≥ 1 and k ≥ 1, gcd(F_{km}/F_m, F_m) divides k.
    Key algebraic identity: F_{km}/F_m ≡ k · F_{m-1}^{k-1} (mod F_m),
    and gcd(F_{m-1}, F_m) = 1.
-/

lemma solution(m k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    Nat.gcd (Nat.fib (k * m) / Nat.fib m) (Nat.fib m) ∣ k := by
  -- By induction on $k$, we can show that $F_{km} \equiv k \cdot F_m \cdot F_{m-1}^{k-1} \pmod{F_m^2}$.
  have h_induction : ∀ k : ℕ, 0 < k → Nat.fib (k * m) ≡ k * Nat.fib m * Nat.fib (m - 1) ^ (k - 1) [MOD Nat.fib m ^ 2] := by
    -- We proceed by induction on $k$.
    intro k hk_pos
    induction' hk_pos with k ih;
    · norm_num [ sq ];
      rfl;
    · -- Using the Fibonacci addition formula, we have $F_{(k+1)m} = F_{km + m} = F_{km}F_{m-1} + F_{km+1}F_m$.
      have h_fib_add : Nat.fib ((k + 1) * m) = Nat.fib (k * m) * Nat.fib (m - 1) + Nat.fib (k * m + 1) * Nat.fib m := by
        cases m <;> simp_all +decide [ Nat.fib_add_two, Nat.succ_mul ];
        exact Nat.fib_add _ _;
      -- Using the induction hypothesis, we have $F_{km+1} \equiv F_{m-1}^k \pmod{F_m}$.
      have h_ind_step : Nat.fib (k * m + 1) ≡ Nat.fib (m - 1) ^ k [MOD Nat.fib m] := by
        refine' Nat.recOn k _ _ <;> simp_all +decide [ Nat.pow_succ', Nat.mul_succ, Nat.fib_add ];
        · rfl;
        · intro n hn; rw [ Nat.succ_mul, Nat.fib_add ] ; simp_all +decide [ ← ZMod.natCast_eq_natCast_iff ] ;
          cases m <;> simp_all +decide [ Nat.fib_add_two, pow_succ' ] ; ring;
      rw [ Nat.modEq_iff_dvd ] at *;
      obtain ⟨ a, ha ⟩ := h_ind_step; obtain ⟨ b, hb ⟩ := ‹ ( fib m ^ 2 : ℤ ) ∣ k * fib m * fib ( m - 1 ) ^ ( k - 1 ) - fib ( k * m ) ›; simp_all +decide [ Nat.succ_mul, pow_succ' ] ;
      rcases k with ( _ | k ) <;> simp_all +decide [ pow_succ' ];
      exact ⟨ b * fib ( m - 1 ) + a, by linear_combination' hb * fib ( m - 1 ) + ha * fib m ⟩;
  -- Dividing both sides of the congruence by $F_m$, we get $F_{km}/F_m \equiv k \cdot F_{m-1}^{k-1} \pmod{F_m}$.
  have h_divided : Nat.fib (k * m) / Nat.fib m ≡ k * Nat.fib (m - 1) ^ (k - 1) [MOD Nat.fib m] := by
    rw [ Nat.modEq_iff_dvd ] at *;
    have := h_induction k hk; rw [ Nat.modEq_iff_dvd ] at this; simp_all +decide [ ← Int.natCast_dvd_natCast, sq, mul_assoc, Nat.mul_div_assoc ] ;
    exact Exists.elim this fun x hx => ⟨ x, by nlinarith [ Nat.div_mul_cancel ( show fib m ∣ fib ( k * m ) from Nat.fib_dvd _ _ ( dvd_mul_left _ _ ) ), Nat.fib_pos.mpr hm ] ⟩;
  -- Since $\gcd(F_{m-1}, F_m) = 1$, it follows that $\gcd(F_{m-1}^{k-1}, F_m) = 1$.
  have h_coprime : Nat.gcd (Nat.fib (m - 1) ^ (k - 1)) (Nat.fib m) = 1 := by
    rcases m with ( _ | _ | m ) <;> simp_all +decide [ Nat.fib_add_two, Nat.gcd_comm ];
    refine' Nat.Coprime.pow_right _ _;
    exact Nat.recOn m ( by norm_num ) fun n ih => by simp_all +decide [ Nat.fib_add_two, Nat.Coprime, Nat.gcd_comm ] ;
  have := h_divided.gcd_eq ; simp_all +decide [ Nat.ModEq, Nat.gcd_comm ];
  exact ( Nat.Coprime.dvd_of_dvd_mul_right ( show Nat.Coprime ( Nat.gcd ( fib m ) ( k * fib ( m - 1 ) ^ ( k - 1 ) ) ) ( fib ( m - 1 ) ^ ( k - 1 ) ) from Nat.Coprime.coprime_dvd_left ( Nat.gcd_dvd_left _ _ ) h_coprime ) <| Nat.gcd_dvd_right _ _ )
