-- Prove2me | solution 1 for BinomialGCDA080170.prime_dvd_choose_primePow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:48:00.113951+00:00
-- url     : https://prove2.me/submissions/8bb55814-1631-45b0-8150-e969d2907b17

-- Sol generated from Novelty/BinomialGCDA080170PrimePower.lean
import Mathlib
import Definitions.Def_Novelty_BinomialGCDA080170

/-!
# The prime-power fibre of OEIS A080170

This companion file extends `Catalog.Novelty.BinomialGCDA080170`.  There the
prime fibre `n = p` was analysed; here we treat the full *prime-power* fibre
`n = p^a`.

The main result `prime_dvd_binomGCD_primePow` shows that for every prime power
`p^a` (with `a ≥ 1`) the binomial gcd `D(p^a - 1)` is divisible by `p`, hence
is nontrivial.  This is the divisibility heart of the (computationally
verified) identity `D(p^a - 1) = p^a`, which is exactly the regime where
Ralf Stephan's closed form *is* correct (see `FUTURE_DIRECTIONS.md`).

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer).  On the prime-power fibre `n = p^a` the gcd should
remain divisible by `p` for every `a`, not just `a = 1`.

EXPERIMENT (Experimenter).  Verified `p ∣ C(q(p^a-1), p^a-1)` for all
`2 ≤ q ≤ p^a` over many `(p, a)` (see `ComputationalEvidence.md`), and proved
it with Kummer's theorem.

ANALYSIS (Analyst).  The key is a *carry at level* `i = v_p(q-1) + 1`.  Since
`p^a - 1 ≡ -1 (mod p^i)` for `i ≤ a`, we have `(p^a-1) % p^i = p^i - 1`, and
`(q-1)(p^a-1) ≡ -(q-1) (mod p^i)`.  Choosing `i` one above the `p`-adic
valuation of `q-1` guarantees `p^i ∤ (q-1)`, so the residue
`(-(q-1)) % p^i ≥ 1` and the carry condition `p^i ≤ (p^i-1) + ((-(q-1)) % p^i)`
holds.  This single carry yields `p ∣ C(q(p^a-1), p^a-1)`.

CRITIQUE (Critic).  The exponent bound `i ≤ a` is essential and uses
`q - 1 < p^a` (from `q ≤ p^a`); without it the residue identity for
`p^a - 1` fails.  The proof is uniform in `q` and `a`, not a finite check.

SYNTHESIS (PI).  Combined with the `a = 1` exactness `p² ∤ D(p-1)` of the
parent file, this pins the qualitative behaviour of `D` on prime powers and
isolates exactly where Stephan's formula succeeds.
-/

open BinomialGCDA080170

open Nat Finset

/-
**Kummer lower bound, prime-power form.**  For a prime `p` and `2 ≤ q ≤ p^a`,
the prime `p` divides `C(q·(p^a - 1), p^a - 1)`.  A carry occurs in base `p` at
digit `v_p(q-1) + 1`.  (For `a = 0` the hypotheses `2 ≤ q ≤ 1` are unsatisfiable,
so no lower bound on `a` is needed.)
-/

/-
**General lower bound on the prime-power fibre.**  `p ∣ D(p^a - 1)` for every
prime `p` and every `a`.  When `a ≥ 1` (so that `p^a - 1` is a genuine A080170
index, with `k ≥ 2` once `p^a ≥ 3`) this shows `D(p^a - 1) > 1`; the divisibility
itself holds for all `a` (the degenerate `D(p^0 - 1) = D(0) = 0` is divisible
by `p`).
-/


open BinomialGCDA080170 in
theorem solution{p a q : ℕ} (hp : p.Prime)
    (hq2 : 2 ≤ q) (hqp : q ≤ p ^ a) :
    p ∣ Nat.choose (q * (p ^ a - 1)) (p ^ a - 1) := by
  have h_kummer : padicValNat p (Nat.choose (q * (p ^ a - 1)) (p ^ a - 1)) ≥ 1 := by
    have h_kummer : padicValNat p (Nat.choose (q * (p ^ a - 1)) (p ^ a - 1)) = Finset.card (Finset.filter (fun i => p ^ i ≤ (p ^ a - 1) % p ^ i + ((q - 1) * (p ^ a - 1)) % p ^ i) (Finset.Ico 1 (Nat.log p (q * (p ^ a - 1)) + 1))) := by
      haveI := Fact.mk hp;
      rw [ show q * ( p ^ a - 1 ) = ( q - 1 ) * ( p ^ a - 1 ) + ( p ^ a - 1 ) by nlinarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ q ), Nat.sub_add_cancel ( by linarith [ Nat.one_le_pow a p hp.pos ] : 1 ≤ p ^ a ) ] ];
      rw [ padicValNat_choose' ];
      exact Nat.lt_succ_self _;
    rw [ h_kummer ];
    refine Finset.card_pos.mpr ⟨ Nat.factorization ( q - 1 ) p + 1, ?_ ⟩ ; simp_all +decide;
    constructor;
    · refine' lt_of_lt_of_le _ ( Nat.log_mono_right <| show q * ( p ^ a - 1 ) ≥ p ^ a from _ );
      · rw [ Nat.log_pow hp.one_lt ];
        contrapose! hqp;
        exact lt_of_le_of_lt ( Nat.pow_le_pow_right hp.pos hqp ) ( Nat.lt_of_le_of_lt ( Nat.le_of_dvd ( Nat.sub_pos_of_lt hq2 ) ( Nat.ordProj_dvd _ _ ) ) ( Nat.pred_lt ( ne_bot_of_gt hq2 ) ) );
      · nlinarith [ Nat.sub_add_cancel ( Nat.one_le_pow a p hp.pos ) ];
    · -- Since $p^i \mid (q-1)$, we have $(q-1) \equiv 0 \pmod{p^i}$, thus $(q-1)*(p^a-1) \equiv 0 \pmod{p^i}$.
      have h_mod : ((q - 1) * (p ^ a - 1)) % p ^ ((q - 1).factorization p + 1) = (p ^ ((q - 1).factorization p + 1) - (q - 1) % p ^ ((q - 1).factorization p + 1)) % p ^ ((q - 1).factorization p + 1) := by
        have h_mod : (q - 1) * (p ^ a - 1) ≡ -(q - 1) [ZMOD p ^ ((q - 1).factorization p + 1)] := by
          rw [ Int.modEq_iff_dvd ];
          exact ⟨ - ( q - 1 ) * p ^ ( a - ( Nat.factorization ( q - 1 ) p + 1 ) ), by rw [ show ( p : ℤ ) ^ a = p ^ ( Nat.factorization ( q - 1 ) p + 1 ) * p ^ ( a - ( Nat.factorization ( q - 1 ) p + 1 ) ) by rw [ ← pow_add, Nat.add_sub_of_le ( show Nat.factorization ( q - 1 ) p + 1 ≤ a from Nat.succ_le_of_lt ( Nat.lt_of_not_ge fun h => by have := Nat.ordProj_dvd ( q - 1 ) p; exact absurd ( Nat.le_of_dvd ( Nat.sub_pos_of_lt hq2 ) this ) ( by linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ q ), pow_le_pow_right₀ hp.one_lt.le h ] ) ) ) ] ] ; ring ⟩;
        zify;
        rw [ Nat.cast_sub <| show ( q - 1 ) % p ^ ( ( q - 1 ).factorization p + 1 ) ≤ p ^ ( ( q - 1 ).factorization p + 1 ) from Nat.le_of_lt <| Nat.mod_lt _ <| pow_pos hp.pos _ ] ; simp_all +decide [ Int.ModEq ];
        cases q <;> simp_all +decide [ Int.emod_eq_emod_iff_emod_sub_eq_zero ];
        rwa [ Nat.cast_sub ( Nat.one_le_pow _ _ hp.pos ) ];
      -- Since $p^i \mid p^a$, we have $(p^a - 1) \equiv -1 \pmod{p^i}$, thus $(p^a - 1) \mod p^i = p^i - 1$.
      have h_mod_pa : (p ^ a - 1) % p ^ ((q - 1).factorization p + 1) = p ^ ((q - 1).factorization p + 1) - 1 := by
        have h_mod_pa : p ^ ((q - 1).factorization p + 1) ∣ p ^ a := by
          refine' pow_dvd_pow _ _;
          exact Nat.succ_le_of_lt ( Nat.lt_of_not_ge fun h => by have := Nat.ordProj_dvd ( q - 1 ) p; exact absurd ( Nat.le_of_dvd ( Nat.sub_pos_of_lt hq2 ) this ) ( by linarith [ Nat.sub_add_cancel ( by linarith : 1 ≤ q ), Nat.pow_le_pow_right hp.one_lt.le h, Nat.sub_add_cancel ( Nat.one_le_pow a p hp.pos ) ] ) );
        obtain ⟨ k, hk ⟩ := h_mod_pa; simp +decide [ hk ] ;
        cases k <;> simp_all +decide [ Nat.mul_succ, Nat.mul_mod ];
        cases k : p ^ ( ( q - 1 ).factorization p + 1 ) <;> simp_all +decide [ Nat.add_mod, Nat.mul_mod ];
      rw [ h_mod, h_mod_pa ];
      rw [ Nat.mod_eq_of_lt ];
      · linarith [ Nat.sub_add_cancel ( Nat.one_le_pow ( ( q - 1 ).factorization p + 1 ) p hp.pos ), Nat.sub_pos_of_lt ( show ( q - 1 ) % p ^ ( ( q - 1 ).factorization p + 1 ) < p ^ ( ( q - 1 ).factorization p + 1 ) from Nat.mod_lt _ ( pow_pos hp.pos _ ) ) ];
      · exact Nat.sub_lt ( pow_pos hp.pos _ ) ( Nat.pos_of_ne_zero fun h => by have := Nat.dvd_of_mod_eq_zero h; exact absurd this ( Nat.pow_succ_factorization_not_dvd ( Nat.sub_ne_zero_of_lt hq2 ) hp ) );
  exact dvd_of_one_le_padicValNat h_kummer
