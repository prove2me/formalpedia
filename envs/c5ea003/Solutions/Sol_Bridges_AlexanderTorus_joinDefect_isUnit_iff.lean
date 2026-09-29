-- Prove2me | solution 1 for Bridges.AlexanderTorus.joinDefect_isUnit_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:59:41.382949+00:00
-- url     : https://prove2.me/submissions/77b3220a-f6f6-470d-9fba-6b05ce8d8ab8

-- Sol generated from Bridges/AlexanderKnotNumberBridgeXI.lean
import Mathlib
import Definitions.Def_Bridges_AlexanderKnotNumberBridgeVII
import Definitions.Def_Bridges_AlexanderKnotNumberBridgeXI
/-
# The knot–number bridge XI: the join defect

Cycle VII proved that `N ↦ A_N` is a **meet**-morphism of the divisor lattice
(`alexander_gcd`) but *not* a join-morphism (`alexander_lcm_not_associated`).  Conjecture
`D1` of `FUTURE_DIRECTIONS.md` asked for the exact size of the failure.  This file closes it.

* `Bridges.AlexanderTorus.alexander_lcm_eq_joinProd` : for odd `M, N > 0`,
  `lcm(A_M, A_N)` is associated to `∏_{d ∣ M or d ∣ N, d > 1} Φ_{2d}` — the join on the
  polynomial side is the product over the *union* of the two divisor sets, whereas
  `A_{lcm(M,N)}` is the product over the divisor set of `lcm(M,N)`, which is generally larger.
* `Bridges.AlexanderTorus.alexander_lcm_mul_joinDefect` : the missing factor is exactly
  `∏_{d ∣ lcm(M,N), d ∤ M, d ∤ N, d > 1} Φ_{2d}`, and
  `Bridges.AlexanderTorus.alexander_lcm_natDegree_add_defect` measures it:
  `deg A_{lcm(M,N)} = deg lcm(A_M, A_N) + ∑_{d} φ(d)` over that same index set.
* `Bridges.AlexanderTorus.joinDefect_isUnit_iff` : the join morphism property holds at
  `(M, N)` precisely when `lcm(M,N)` has no divisor `> 1` outside `divisors M ∪ divisors N`.
* `Bridges.AlexanderTorus.joinDefect_three_five_natDegree` : the numerical instance behind
  cycle VII's counterexample — the defect for `(3,5)` is `Φ_30`, of degree `φ(15) = 8`,
  and indeed `14 = 6 + 8`.

Everything reduces, as predicted, to the Finset identity
`(∏_{s ∪ t}) · (∏_{s ∩ t}) = (∏_s) · (∏_t)` together with `divisors (gcd M N) =
divisors M ∩ divisors N`.
-/

open Bridges.AlexanderTorus

open Polynomial Finset

/-! ## Divisor sets of gcd's and lcm's -/



lemma mem_unionIdx {M N d : ℕ} :
    d ∈ unionIdx M N ↔ d ≠ 1 ∧ (d ∣ M ∧ M ≠ 0 ∨ d ∣ N ∧ N ≠ 0) := by
  simp [unionIdx, Finset.mem_erase, Nat.mem_divisors]




/-! ## The join on the polynomial side -/


/-! ## The join defect -/





/-! ## Degrees -/






/-! ## The numerical instance behind cycle VII's counterexample -/



open Bridges.AlexanderTorus in
theorem solution{M N : ℕ} (hM : Odd M) (hN : Odd N)
    (hMpos : 0 < M) (hNpos : 0 < N) :
    IsUnit (joinDefect M N)
      ↔ ∀ d, d ∣ Nat.lcm M N → d ≠ 1 → d ∣ M ∨ d ∣ N := by
  have hL : Odd (Nat.lcm M N) := by
    rcases hM with ⟨a, ha⟩
    rcases hN with ⟨b, hb⟩
    refine Nat.odd_iff.2 ?_
    have h2 : ¬ (2 ∣ Nat.lcm M N) := by
      intro h2
      rcases (Nat.Prime.dvd_mul Nat.prime_two).1 (h2.trans (Nat.lcm_dvd_mul M N)) with h | h
      · omega
      · omega
    omega
  have hLpos : 0 < Nat.lcm M N := Nat.pos_of_ne_zero (fun h => by
    simp [Nat.lcm_eq_zero_iff, hMpos.ne', hNpos.ne'] at h)
  constructor
  · intro hu d hdL hd1
    by_contra hcon
    push_neg at hcon
    have hnotmem : d ∉ unionIdx M N := by
      rw [mem_unionIdx]
      rintro ⟨-, ⟨hdm, -⟩ | ⟨hdn, -⟩⟩
      · exact hcon.1 hdm
      · exact hcon.2 hdn
    have hmem : d ∈ ((Nat.lcm M N).divisors.erase 1) \ unionIdx M N :=
      Finset.mem_sdiff.2 ⟨Finset.mem_erase.2 ⟨hd1, Nat.mem_divisors.2 ⟨hdL, hLpos.ne'⟩⟩, hnotmem⟩
    -- a cyclotomic factor of the defect is not a unit
    have hdvd : cyclotomic (2 * d) ℤ ∣ joinDefect M N := Finset.dvd_prod_of_mem _ hmem
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdL hLpos
    have : IsUnit (cyclotomic (2 * d) ℤ) := isUnit_of_dvd_unit hdvd hu
    exact (cyclotomic.irreducible (n := 2 * d) (by omega)).not_isUnit this
  · intro h
    have hempty : ((Nat.lcm M N).divisors.erase 1) \ unionIdx M N = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun d hd => ?_
      rw [Finset.mem_sdiff, Finset.mem_erase, Nat.mem_divisors, mem_unionIdx] at hd
      obtain ⟨⟨hd1, hdL, -⟩, hnot⟩ := hd
      refine hnot ⟨hd1, ?_⟩
      rcases h d hdL hd1 with hdm | hdn
      · exact Or.inl ⟨hdm, hMpos.ne'⟩
      · exact Or.inr ⟨hdn, hNpos.ne'⟩
    rw [joinDefect, hempty, Finset.prod_empty]
    exact isUnit_one
