-- Prove2me | solution 1 for Bridges.AlexanderTorus.isRelPrime_cyclotomic_zmod_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T06:28:00.635834+00:00
-- url     : https://prove2.me/submissions/6a3d2e17-5c6f-4ca4-b258-399bf5219e79

import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridgeXII

open Bridges.AlexanderTorus Polynomial Finset in
theorem solution {ℓ : ℕ} [Fact (Nat.Prime ℓ)] {N : ℕ} (hN : Odd N) (hl : ¬ ℓ ∣ 2 * N)
    {d e : ℕ} (hd : d ∈ N.divisors.erase 1) (he : e ∈ N.divisors.erase 1) (hde : d ≠ e) :
    IsRelPrime (cyclotomic (2 * d) (ZMod ℓ)) (cyclotomic (2 * e) (ZMod ℓ)) := by
  have hNpos : 0 < N := hN.pos
  have hn : 0 < 2 * N := by omega
  -- `X^(2N) - 1` is squarefree when `ℓ ∤ 2N`
  have hsep : (X ^ (2 * N) - 1 : (ZMod ℓ)[X]).Separable := by
    rw [X_pow_sub_one_separable_iff]
    intro h0
    exact hl ((ZMod.natCast_eq_zero_iff _ _).1 (by exact_mod_cast h0))
  have hsq := hsep.squarefree
  obtain ⟨-, hdN⟩ := mem_erase.1 hd
  obtain ⟨-, heN⟩ := mem_erase.1 he
  have hdd : 2 * d ∈ (2 * N).divisors :=
    Nat.mem_divisors.2 ⟨Nat.mul_dvd_mul_left 2 (Nat.dvd_of_mem_divisors hdN), by omega⟩
  have hee : 2 * e ∈ (2 * N).divisors :=
    Nat.mem_divisors.2 ⟨Nat.mul_dvd_mul_left 2 (Nat.dvd_of_mem_divisors heN), by omega⟩
  have hne : 2 * d ≠ 2 * e := by omega
  -- both cyclotomic factors divide `X^(2N) - 1`, as distinct factors of its product
  have hdvd : cyclotomic (2 * d) (ZMod ℓ) * cyclotomic (2 * e) (ZMod ℓ) ∣ X ^ (2 * N) - 1 := by
    have hpair : ∏ i ∈ ({2 * d, 2 * e} : Finset ℕ), cyclotomic i (ZMod ℓ)
        = cyclotomic (2 * d) (ZMod ℓ) * cyclotomic (2 * e) (ZMod ℓ) := prod_pair hne
    rw [← prod_cyclotomic_eq_X_pow_sub_one hn, ← hpair]
    refine prod_dvd_prod_of_subset _ _ _ ?_
    intro i hi
    rw [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hdd
    · exact hee
  have hsq2 := Squarefree.squarefree_of_dvd hdvd hsq
  intro f hf1 hf2
  exact hsq2 f (mul_dvd_mul hf1 hf2)
