-- Prove2me | solution 1 for Bridges.AlexanderTorus.isRelPrime_excess
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T03:18:09.626291+00:00
-- url     : https://prove2.me/submissions/9fd3ebf2-8bb5-4284-a6d5-474143c932d9

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridgeVII
open Bridges.AlexanderTorus Polynomial in
theorem solution {M N : ℕ} (hMpos : 0 < M) (hNpos : 0 < N) :
    IsRelPrime (excess (Nat.gcd M N) M) (excess (Nat.gcd M N) N) := by
  -- distinct cyclotomic polynomials over `ℤ` are non-associated irreducibles
  have hpair : ∀ a b : ℕ, 0 < a → 0 < b → a ≠ b →
      IsRelPrime (cyclotomic a ℤ) (cyclotomic b ℤ) := by
    intro a b ha hb hab
    rw [(cyclotomic.irreducible ha).isRelPrime_iff_not_dvd]
    intro hdvd
    have hassoc := (cyclotomic.irreducible ha).associated_of_dvd (cyclotomic.irreducible hb) hdvd
    have heq := eq_of_monic_of_associated (cyclotomic.monic a ℤ) (cyclotomic.monic b ℤ) hassoc
    exact hab (cyclotomic_injective heq)
  unfold excess
  refine IsRelPrime.prod_left fun d hd => IsRelPrime.prod_right fun e he => ?_
  simp only [Finset.mem_sdiff, Finset.mem_erase, Nat.mem_divisors] at hd he
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd.1.2.1 hMpos
  have he0 : 0 < e := Nat.pos_of_dvd_of_pos he.1.2.1 hNpos
  refine hpair (2 * d) (2 * e) (by omega) (by omega) fun h => ?_
  -- a common index would divide `gcd M N`, but the excess removes those
  have hde : d = e := by omega
  subst hde
  exact hd.2 ⟨hd.1.1, Nat.dvd_gcd hd.1.2.1 he.1.2.1, (Nat.gcd_pos_of_pos_left N hMpos).ne'⟩
