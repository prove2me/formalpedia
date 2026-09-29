-- Prove2me | solution 1 for primPart_coprime_proper_divs
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T02:15:18.931196+00:00
-- url     : https://prove2.me/submissions/c307c5d2-8126-46fb-bf61-3f33624520c0

-- Sol generated from Shared/NumberTheory/CarmichaelProof.lean
import Mathlib
import Definitions.Def_Shared_NumberTheory_CarmichaelProof
-- [catalogfix] missing module: import Shared.NumberTheory.CarmichaelHelper

/-! # Certified finite range of Carmichael's theorem (composite case)

We prove that every composite `n` with `13 ≤ n ≤ 10000` gives `F(n)` a
primitive prime divisor.
-/

set_option maxHeartbeats 800000

/-! ## Bridge Lemma -/


/-! ## Computational verification infrastructure -/




/-! ## Correctness lemmas -/

lemma stripAllAux_dvd (r m fuel : ℕ) : stripAllAux r m fuel ∣ r := by
  induction fuel generalizing r with
  | zero => exact dvd_refl r
  | succ fuel ih =>
    simp only [stripAllAux]
    split_ifs with h1 h2
    · exact dvd_refl r
    · exact dvd_refl r
    · exact dvd_trans (ih (r / Nat.gcd r m)) (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left r m))

lemma stripAllAux_coprime (r m fuel : ℕ) (hm : 1 < m) (hr : 0 < r) (hfuel : r ≤ fuel) :
    Nat.gcd (stripAllAux r m fuel) m = 1 := by
  induction' fuel with fuel ih generalizing r m;
  · grind +qlia;
  · by_cases hgr : Nat.gcd r m > 1;
    · convert ih ( r / Nat.gcd r m ) m hm ( Nat.div_pos ( Nat.le_of_dvd hr ( Nat.gcd_dvd_left _ _ ) ) hgr.le ) _ using 1;
      · have h1 : ¬(m ≤ 1) := by omega
        have h2 : ¬(Nat.gcd r m ≤ 1) := by omega
        simp only [stripAllAux, if_neg h1, if_neg h2]
      · exact Nat.le_of_lt_succ ( Nat.div_lt_of_lt_mul <| by nlinarith [ Nat.div_mul_cancel ( Nat.gcd_dvd_left r m ) ] );
    · interval_cases _ : Nat.gcd r m <;> simp_all +decide [ stripAllAux ]




/-! ## Computational verification -/


/-! ## The composite case -/


lemma solution(n : ℕ) (hpp : 1 < primPart n) (d : ℕ)
    (hd : d ∈ propDivs n) : ¬((primPart n).minFac ∣ Nat.fib d) := by
  have h_coprime : Nat.gcd (primPart n) (Nat.fib d) = 1 := by
    have h_coprime : ∀ l : List ℕ, d ∈ l → Nat.gcd (List.foldl (fun r d => stripAllAux r (Nat.fib d) r) (Nat.fib n) l) (Nat.fib d) = 1 := by
      intros l hl; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ Nat.gcd_comm ] ;
      by_cases h : Nat.fib ih > 1 <;> by_cases h' : 0 < List.foldl ( fun r d => stripAllAux r ( Nat.fib d ) r ) ( Nat.fib n ) l <;> simp_all +decide [ Nat.gcd_comm ];
      · have := stripAllAux_coprime ( List.foldl ( fun r d => stripAllAux r ( Nat.fib d ) r ) ( Nat.fib n ) l ) ( Nat.fib ih ) ( List.foldl ( fun r d => stripAllAux r ( Nat.fib d ) r ) ( Nat.fib n ) l ) h h' ( by linarith ) ; simp_all +decide [ Nat.gcd_comm ] ;
        cases hl <;> simp_all +decide [ Nat.gcd_comm ];
        exact Nat.Coprime.coprime_dvd_right ( stripAllAux_dvd _ _ _ ) ‹_›;
      · have h_contra : ∀ l : List ℕ, List.foldl (fun r d => stripAllAux r (Nat.fib d) r) (Nat.fib n) l = 0 → False := by
          intros l hl; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ Nat.gcd_comm ] ;
          have := stripAllAux_dvd ( List.foldl ( fun r d => stripAllAux r ( Nat.fib d ) r ) ( Nat.fib n ) l ) ( Nat.fib ih ) ( List.foldl ( fun r d => stripAllAux r ( Nat.fib d ) r ) ( Nat.fib n ) l ) ; simp_all +decide [ Nat.gcd_comm ] ;
        exact False.elim <| h_contra l h';
      · rcases ih with ( _ | _ | ih ) <;> simp_all +arith +decide [ Nat.fib_add_two ];
        · cases hl <;> simp_all +decide [ propDivs ];
          unfold stripAllAux; aesop;
        · unfold stripAllAux; aesop;
        · rcases ih with ( _ | _ | ih ) <;> simp_all +arith +decide [ Nat.fib_add_two ];
          · unfold stripAllAux; aesop;
          · linarith [ Nat.fib_pos.2 ( Nat.succ_pos ih ) ];
      · have h_contra : List.foldl (fun r d => stripAllAux r (Nat.fib d) r) (Nat.fib n) l ∣ Nat.fib n := by
          have h_contra : ∀ l : List ℕ, List.foldl (fun r d => stripAllAux r (Nat.fib d) r) (Nat.fib n) l ∣ Nat.fib n := by
            intro l; induction' l using List.reverseRecOn with l ih <;> simp_all +decide [ Nat.gcd_comm ] ;
            exact dvd_trans ( stripAllAux_dvd _ _ _ ) ‹_›;
          exact h_contra l;
        rcases n with ( _ | _ | n ) <;> simp_all +decide [ Nat.fib_add_two ];
    exact h_coprime _ hd;
  exact fun h => Nat.Prime.not_dvd_one ( Nat.minFac_prime hpp.ne' ) ( h_coprime ▸ Nat.dvd_gcd ( Nat.minFac_dvd _ ) h )
