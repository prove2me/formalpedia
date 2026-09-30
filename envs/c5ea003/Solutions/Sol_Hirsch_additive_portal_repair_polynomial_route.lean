-- Prove2me | solution 1 for Hirsch.additive_portal_repair_polynomial_route
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-12T23:50:49.46388+00:00
-- url     : https://prove2.me/submissions/2a2dd9bd-9ee5-43fa-bc04-def26a5a2a98

import Mathlib
import Definitions.Def_Hirsch_additive_portal_repair
open scoped BigOperators
open HirschRegionRoute HirschAdditiveAllowance

open Set

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschProduct

/-- Concatenate padded walks. This is independent of polytope geometry. -/
lemma append_walk {E : Type*} (R : E → E → Prop)
    {u v z : E} {A B : ℕ}
    (p q : ℕ → E)
    (hp0 : p 0 = u) (hpA : p A = v)
    (hq0 : q 0 = v) (hqB : q B = z)
    (hp : ∀ j < A, p j = p (j + 1) ∨ R (p j) (p (j + 1)))
    (hq : ∀ j < B, q j = q (j + 1) ∨ R (q j) (q (j + 1))) :
    ∃ w : ℕ → E, w 0 = u ∧ w (A + B) = z ∧
      ∀ j < A + B, w j = w (j + 1) ∨ R (w j) (w (j + 1)) := by
  let w : ℕ → E := fun j => if j < A then p j else q (j - A)
  have hleft (j : ℕ) (hj : j ≤ A) : w j = p j := by
    by_cases h : j < A
    · simp only [w, if_pos h]
    · have heq : j = A := by omega
      subst j
      simp only [w, lt_self_iff_false, if_false, Nat.sub_self, hq0, hpA]
  have hright (j : ℕ) (hj : A ≤ j) : w j = q (j - A) := by
    exact if_neg (by omega)
  refine ⟨w, (hleft 0 (Nat.zero_le A)).trans hp0, ?_, ?_⟩
  · rw [hright (A + B) (by omega), Nat.add_sub_cancel_left]
    exact hqB
  · intro j hj
    by_cases hjA : j < A
    · rw [hleft j (by omega), hleft (j + 1) (by omega)]
      exact hp j hjA
    · rw [hright j (by omega), hright (j + 1) (by omega)]
      have hidx : j + 1 - A = (j - A) + 1 := by omega
      rw [hidx]
      exact hq (j - A) (by omega)


end HirschProduct
end

/-!
# Cross-level accounting for finite ordinary-edge repair certificates

A node records its actual first edge and child repairs. Leaves are stationary
or actual edges, not a conjectural diameter oracle. Its charge is the POSITIVE
increase of 1+sum(child dimension*excess) over parent dimension*excess.
The theorem proves both an actual assembled route and its telescoping bound.
Dimension drops ensure the intended geometric recursion is well founded.

New proof candidate. No Lean compilation or platform acceptance is asserted.
-/
open scoped BigOperators
open Set HirschRegionRoute
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace HirschAmortized

variable {V : Type*} (R : V → V → Prop)

lemma append_routes {a b c : V} {A B : ℕ}
    (h₁ : Route R A a b) (h₂ : Route R B b c) : Route R (A+B) a c := by
  obtain ⟨w, hw0, hwA, hws⟩ := h₁
  obtain ⟨z, hz0, hzB, hzs⟩ := h₂
  exact HirschProduct.append_walk R w z hw0 hwA hz0 hzB hws hzs

lemma single_route {a b : V} (h : a=b ∨ R a b) : Route R 1 a b := by
  refine ⟨fun j => if j=0 then a else b, by simp, by simp, ?_⟩
  intro j hj
  have he : j=0 := by omega
  simpa [he] using h

/-- Finite chain adapter with different costs at each actual pair. -/
theorem route_chain (n : ℕ) (p : ℕ → V) (cost : Fin n → ℕ)
    (h : ∀ i : Fin n, Route R (cost i) (p i.val) (p (i.val+1))) :
    Route R (∑ i, cost i) (p 0) (p n) := by
  induction n generalizing p with
  | zero =>
    simpa using (show Route R 0 (p 0) (p 0) from
      ⟨fun _ => p 0, rfl, rfl, by intro j hj; omega⟩)
  | succ n ih =>
    have ht := ih (fun j => p (j+1)) (fun i => cost i.succ)
      (fun i => by simpa [Nat.add_assoc] using h i.succ)
    have hf := h (0 : Fin (n+1))
    have ha := append_routes R hf ht
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using ha


end HirschAmortized

/-!
# Bounded additive excess overspending does not multiply across levels

Suppose each child excess is at most its parent's e, siblings total at most
 e+b, and dimensions strictly drop. Stop at excess <=b, with known leaf rate C.
Then actual edge cost is at most

  C*e + (1+b*C)*h*(e-b).

Natural subtraction truncates. The proof conserves SHIFTED excess on the
large-child skeleton; it does not multiply a factor-three bound per level.
The geometric availability of such splits is not asserted universally.
New source: no local Lean or Prove2Me verdict is claimed.
-/
open scoped BigOperators
open HirschRegionRoute HirschAmortized
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace HirschAdditiveAllowance

/-- At most one large child is controlled by monotonicity. At least two are
controlled by the sibling sum; subtracting b per large child pays the spill. -/
theorem shifted_child_excess_conserved
    (n e b : ℕ) (mass : Fin n → ℕ)
    (hmono : ∀ i, mass i ≤ e) (hsum : (∑ i, mass i) ≤ e+b) :
    (∑ i, (mass i-b)) ≤ e-b := by
  classical
  let S := Finset.univ.filter (fun i : Fin n => b < mass i)
  have hshift : (∑ i, (mass i-b)) = ∑ i ∈ S, (mass i-b) := by
    symm
    simp only [S, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : b < mass i
    · simp [hi]
    · have hle : mass i ≤ b := by omega
      simp [hi, Nat.sub_eq_zero_of_le hle]
  by_cases hsmall : S.card ≤ 1
  · by_cases hn : S.Nonempty
    · obtain ⟨i, hi⟩ := hn
      have heq : S = {i} := by
        ext j
        constructor
        · intro hj
          exact Finset.mem_singleton.mpr ((Finset.card_le_one.mp hsmall) j hj i hi)
        · intro hj
          have hji := Finset.mem_singleton.mp hj
          simpa [hji] using hi
      rw [hshift, heq]
      simpa using Nat.sub_le_sub_right (hmono i) b
    · have heq := Finset.not_nonempty_iff_eq_empty.mp hn
      rw [hshift, heq]
      simp
  · have hcard : 2 ≤ S.card := by omega
    have hsplit : (∑ i ∈ S, (mass i-b)) + S.card*b = ∑ i ∈ S, mass i := by
      calc
        (∑ i ∈ S, (mass i-b)) + S.card*b = ∑ i ∈ S, ((mass i-b)+b) := by
          simp [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        _ = ∑ i ∈ S, mass i := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Nat.sub_add_cancel (le_of_lt (Finset.mem_filter.mp hi).2)
    have hsub : (∑ i ∈ S, mass i) ≤ ∑ i, mass i := by
      simp only [S, Finset.sum_filter]
      exact Finset.sum_le_sum (fun i _ => by split_ifs <;> omega)
    have htwice : 2*b ≤ S.card*b := Nat.mul_le_mul_right b hcard
    have ht := hsub.trans hsum
    rw [← hsplit] at ht
    rw [hshift]
    omega

def allowanceBudget (C b h e : ℕ) : ℕ := C*e+(1+b*C)*h*(e-b)

/-- The whole recurrence closes with a fixed polynomial once additive
overspending b and the small-leaf rate C are fixed. -/
theorem additive_allowance_node_bound
    (n h e b C : ℕ) (dims mass costs : Fin n → ℕ)
    (he : b < e) (hh : 0 < h)
    (hdrop : ∀ i, dims i < h) (hmono : ∀ i, mass i ≤ e)
    (hsum : (∑ i, mass i) ≤ e+b)
    (hcost : ∀ i, costs i ≤ allowanceBudget C b (dims i) (mass i)) :
    1+(∑ i, costs i) ≤ allowanceBudget C b h e := by
  have hshift := shifted_child_excess_conserved n e b mass hmono hsum
  have hweighted : (∑ i, dims i*(mass i-b)) ≤ (h-1)*(e-b) := by
    have hs : (∑ i, dims i*(mass i-b)) ≤ (h-1)*(∑ i, (mass i-b)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_right (mass i-b)
        (by have hi := hdrop i; omega))
    exact hs.trans (Nat.mul_le_mul_left (h-1) hshift)
  have hc : (∑ i, costs i) ≤ C*(∑ i, mass i) + (1+b*C)*(∑ i, dims i*(mass i-b)) := by
    have hs : (∑ i, costs i) ≤ ∑ i, allowanceBudget C b (dims i) (mass i) :=
      Finset.sum_le_sum (fun i _ => hcost i)
    simpa [allowanceBudget, Finset.sum_add_distrib, Finset.mul_sum, Nat.mul_assoc] using hs
  have hm := Nat.mul_le_mul_left C hsum
  have hw := Nat.mul_le_mul_left (1+b*C) hweighted
  have hz : 1 ≤ e-b := by omega
  have hpay : 1+b*C ≤ (1+b*C)*(e-b) := by
    simpa using Nat.mul_le_mul_left (1+b*C) hz
  have hid : (1+b*C)*(h-1)*(e-b)+(1+b*C)*(e-b) = (1+b*C)*h*(e-b) := by
    have hh' : h-1+1=h := by omega
    calc
      (1+b*C)*(h-1)*(e-b)+(1+b*C)*(e-b) = (1+b*C)*(h-1+1)*(e-b) := by ring
      _ = (1+b*C)*h*(e-b) := by rw [hh']
  simp only [Nat.mul_add] at hm
  rw [Nat.mul_comm C b] at hm
  unfold allowanceBudget
  simp only [Nat.mul_assoc] at hw hid ⊢
  omega

variable {V : Type*}

/-- Small leaves carry an actual certified route. Only their established
excess-threshold bound is used; no high-dimensional routing oracle is added. -/
theorem AdditiveRepair.sound
    {R : V → V → Prop} {b C h e cost : ℕ} {x y : V}
    (cert : AdditiveRepair R b C x y h e cost) :
    Route R cost x y ∧ cost ≤ allowanceBudget C b h e := by
  induction cert with
  | leaf x y h e cost he hr hc =>
    exact ⟨hr, by simpa [allowanceBudget, Nat.sub_eq_zero_of_le he] using hc⟩
  | node h e n u p dims mass costs he hh hfirst hdrop hmono hsum children ih =>
    refine ⟨append_routes R (single_route R hfirst)
      (route_chain R n p costs (fun i => (ih i).1)), ?_⟩
    exact additive_allowance_node_bound n h e b C dims mass costs he hh hdrop hmono hsum
      (fun i => (ih i).2)

end HirschAdditiveAllowance

theorem solution {V : Type*} {R : V → V → Prop} {b C h e cost : ℕ} {x y : V}
    (cert : HirschAdditiveAllowance.AdditiveRepair R b C x y h e cost) :
    HirschRegionRoute.Route R cost x y ∧ cost ≤ C*e+(1+b*C)*h*(e-b) := by
  simpa only [allowanceBudget] using cert.sound
