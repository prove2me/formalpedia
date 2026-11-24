-- Prove2me | solution 1 for SingularModuli.card_range_filter_crt
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T22:57:24.465052+00:00
-- url     : https://prove2.me/submissions/fd96e419-1f98-41ac-9e81-c22381fcecf4

import Mathlib
import Definitions.Def_Cryptography_SingularModuli_GcdCriterion
import Definitions.Def_Cryptography_SingularModuli_RootCount

open SingularModuli

namespace SingularModuli

theorem solution {p q : ℕ} [NeZero p] [NeZero q] (hcop : Nat.Coprime p q)
    (R : ZMod p → ZMod q → Prop) [∀ a b, Decidable (R a b)] :
    ((Finset.range (p * q)).filter (fun j : ℕ => R (j : ZMod p) (j : ZMod q))).card
      = (Finset.univ.filter (fun z : ZMod p × ZMod q => R z.1 z.2)).card := by
  classical
  refine Finset.card_bij (fun j _ => ((j : ZMod p), (j : ZMod q))) ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hj.2⟩
  · intro j1 hj1 j2 hj2 heq
    have hj1lt : j1 < p * q := Finset.mem_range.mp (Finset.mem_filter.mp hj1).1
    have hj2lt : j2 < p * q := Finset.mem_range.mp (Finset.mem_filter.mp hj2).1
    have hp1 : j1 ≡ j2 [MOD p] := ZMod.natCast_eq_natCast_iff _ _ p |>.mp (Prod.ext_iff.mp heq).1
    have hq1 : j1 ≡ j2 [MOD q] := ZMod.natCast_eq_natCast_iff _ _ q |>.mp (Prod.ext_iff.mp heq).2
    exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hp1, hq1⟩ |>.eq_of_lt_of_lt hj1lt hj2lt
  · intro z hz
    have h1 : ((Nat.chineseRemainder hcop z.1.val z.2.val).1 : ZMod p) = z.1 :=
      calc ((Nat.chineseRemainder hcop z.1.val z.2.val).1 : ZMod p)
          = ((z.1.val : ℕ) : ZMod p) :=
            ZMod.natCast_eq_natCast_iff _ _ p |>.mpr
              (Nat.chineseRemainder hcop z.1.val z.2.val).2.1
        _ = z.1 := ZMod.natCast_zmod_val z.1
    have h2 : ((Nat.chineseRemainder hcop z.1.val z.2.val).1 : ZMod q) = z.2 :=
      calc ((Nat.chineseRemainder hcop z.1.val z.2.val).1 : ZMod q)
          = ((z.2.val : ℕ) : ZMod q) :=
            ZMod.natCast_eq_natCast_iff _ _ q |>.mpr
              (Nat.chineseRemainder hcop z.1.val z.2.val).2.2
        _ = z.2 := ZMod.natCast_zmod_val z.2
    have hlt : (Nat.chineseRemainder hcop z.1.val z.2.val).1 < p * q :=
      Nat.chineseRemainder_lt_mul hcop _ _ (NeZero.ne p) (NeZero.ne q)
    refine ⟨(Nat.chineseRemainder hcop z.1.val z.2.val).1, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr hlt,
        by rw [h1, h2]; exact (Finset.mem_filter.mp hz).2⟩
    · exact Prod.ext h1 h2

end SingularModuli

open SingularModuli

theorem solution {p q : ℕ} [NeZero p] [NeZero q] (hcop : Nat.Coprime p q)
    (R : ZMod p → ZMod q → Prop) [∀ a b, Decidable (R a b)] :
    ((Finset.range (p * q)).filter (fun j : ℕ => R (j : ZMod p) (j : ZMod q))).card
      = (Finset.univ.filter (fun z : ZMod p × ZMod q => R z.1 z.2)).card :=
  SingularModuli.solution hcop R

#print axioms solution
