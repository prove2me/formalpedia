-- Prove2me | solution 1 for Shamir1979.reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:03:11.936588+00:00
-- url     : https://prove2.me/submissions/b1d38d17-c5c9-49f5-9c75-60956c27fce0

import Mathlib
import Definitions.Def_Shamir1979_Model
open scoped BigOperators
universe u
open Shamir1979

namespace S108Sh

theorem deg_lt (p k : Nat) [Fact (Nat.Prime p)] (secret : ZMod p) (coins : Coins p k) (hk : 0 < k) :
    (sharingPolynomial secret coins).degree < (k : WithBot ℕ) := by
  unfold sharingPolynomial
  have hk' : (k : WithBot ℕ) = ((k - 1 + 1 : ℕ) : WithBot ℕ) := by congr 1; omega
  rw [hk']
  refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
  · exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast Nat.succ_pos _)
  · refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (by exact WithBot.bot_lt_coe _)]
    intro j _
    refine lt_of_le_of_lt (Polynomial.degree_monomial_le _ _) ?_
    exact_mod_cast (by omega : j.val + 1 < k - 1 + 1)

theorem eval0 (p k : Nat) [Fact (Nat.Prime p)] (secret : ZMod p) (coins : Coins p k) :
    (sharingPolynomial secret coins).eval 0 = secret := by
  unfold sharingPolynomial
  simp [Polynomial.eval_finsetSum]

theorem point_inj (p n : Nat) (hnp : n < p) :
    Function.Injective (fun i : Fin n => point (p := p) i) := by
  intro i j h
  simp only [point] at h
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  exact Fin.ext (by omega)

end S108Sh

open S108Sh

theorem solution (p n k : Nat) [Fact (Nat.Prime p)]
    (hk : 0 < k) (hkn : k ≤ n) (hnp : n < p)
    (secret : ZMod p) (coins : Coins p k) (Γ : Finset (Fin n)) (hΓ : k ≤ Γ.card) :
    recover Γ (observe Γ secret coins) = secret := by
  classical
  set f := sharingPolynomial secret coins with hf
  have hinj : Set.InjOn (fun i : Fin n => point (p := p) i) Γ :=
    (point_inj p n hnp).injOn
  have hdeg : f.degree < Γ.card :=
    lt_of_lt_of_le (deg_lt p k secret coins hk) (by exact_mod_cast hΓ)
  have hI := Lagrange.eq_interpolate_of_eval_eq (s := Γ) (v := fun i : Fin n => point (p := p) i)
    (r := fun i => f.eval (point (p := p) i)) hinj hdeg (fun i _ => rfl)
  have h0 : f.eval 0 = secret := eval0 p k secret coins
  have key : f.eval 0 = ∑ i ∈ Γ, f.eval (point (p := p) i) *
      ∏ j ∈ Γ.erase i, ((point (p := p) i - point (p := p) j)⁻¹ * (0 - point (p := p) j)) := by
    conv_lhs => rw [hI]
    simp [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, Lagrange.basis,
      Polynomial.eval_prod, Lagrange.basisDivisor]
  refine Eq.trans ?_ (key.symm.trans h0)
  unfold recover
  rw [← Finset.sum_coe_sort Γ]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp only [observe, share]
  congr 1
  rw [← Finset.prod_coe_sort (Γ.erase i.val)]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), if_pos rfl, one_mul]
  refine Finset.prod_bij (fun j hj => ⟨j.val, Finset.mem_erase.mpr
      ⟨fun h => (Finset.mem_erase.mp hj).1 (Subtype.ext h), j.2⟩⟩) ?_ ?_ ?_ ?_
  · intro a _; simp
  · intro a ha b hb h; exact Subtype.ext (by simpa using congrArg Subtype.val h)
  · intro b _
    refine ⟨⟨b.val, (Finset.mem_erase.mp b.2).2⟩, Finset.mem_erase.mpr ⟨fun h => ?_, Finset.mem_univ _⟩, rfl⟩
    exact (Finset.mem_erase.mp b.2).1 (congrArg Subtype.val h)
  · intro a ha
    have hne : a ≠ i := (Finset.mem_erase.mp ha).1
    rw [if_neg hne]
    simp [div_eq_mul_inv, mul_comm]
