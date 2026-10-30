-- Prove2me | solution 1 for Shamir1979.privacy_fiber_count
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:06:16.321346+00:00
-- url     : https://prove2.me/submissions/f6dadfdc-8640-42c6-8655-451f899d1139

import Mathlib
import Definitions.Def_Shamir1979_Model
open scoped BigOperators
universe u

open Shamir1979

noncomputable section
set_option maxHeartbeats 400000
namespace S108Sh
open Polynomial

lemma point_ne_zero {p n : Nat} [Fact (Nat.Prime p)] (hnp : n < p) (i : Fin n) :
    point (p := p) i ≠ 0 := by
  unfold point
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have := Nat.le_of_dvd (Nat.succ_pos _) h
  omega

lemma point_inj {p n : Nat} [Fact (Nat.Prime p)] (hnp : n < p) {i j : Fin n}
    (h : point (p := p) i = point (p := p) j) : i = j := by
  unfold point at h
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  ext; omega

/-- the linear part -/
def L (p n k : Nat) (Γ : Finset (Fin n)) (c : Coins p k) : Observation p Γ :=
  fun i => (∑ j : Fin (k-1), monomial (j.val+1) (c j)).eval (point (p := p) i.val)

def Lh (p n k : Nat) (Γ : Finset (Fin n)) : Coins p k →+ Observation p Γ where
  toFun := L p n k Γ
  map_zero' := by funext i; simp [L]
  map_add' a b := by
    funext i
    simp only [L, Pi.add_apply, map_add, Finset.sum_add_distrib, eval_add]

lemma observe_eq {p n k : Nat} (Γ : Finset (Fin n)) (secret : ZMod p) (c : Coins p k) :
    observe Γ secret c = fun i => secret + L p n k Γ c i := by
  funext i
  simp [observe, share, sharingPolynomial, L, eval_add]

lemma L_surj {p n k : Nat} [Fact (Nat.Prime p)] (hk : 0 < k) (hnp : n < p)
    (Γ : Finset (Fin n)) (hΓ : Γ.card < k) : Function.Surjective (L p n k Γ) := by
  classical
  intro y
  let v : Option {i // i ∈ Γ} → ZMod p := fun o => o.elim 0 (fun i => point (p := p) i.val)
  let r : Option {i // i ∈ Γ} → ZMod p := fun o => o.elim 0 y
  have hinj : Set.InjOn v (Finset.univ : Finset (Option {i // i ∈ Γ})) := by
    intro a _ b _ h
    rcases a with _ | a <;> rcases b with _ | b
    · rfl
    · exact absurd h.symm (point_ne_zero hnp _)
    · exact absurd h (point_ne_zero hnp _)
    · simp only [v, Option.elim] at h
      exact congrArg some (Subtype.ext (point_inj hnp h))
  set Q := Lagrange.interpolate (Finset.univ : Finset (Option {i // i ∈ Γ})) v r with hQ
  have hdeg : Q.degree < k := by
    have := Lagrange.degree_interpolate_lt (r := r) hinj
    rw [Finset.card_univ, Fintype.card_option, Fintype.card_coe] at this
    calc Q.degree < ((Γ.card + 1 : ℕ) : WithBot ℕ) := this
      _ ≤ k := by exact_mod_cast (by omega : Γ.card + 1 ≤ k)
  have hnd : Q.natDegree < k := by
    rcases eq_or_ne Q 0 with h | h
    · rw [h]; simpa using hk
    · exact (natDegree_lt_iff_degree_lt h).2 hdeg
  have h0 : Q.eval 0 = 0 := by
    exact Lagrange.eval_interpolate_at_node (r := r) hinj (Finset.mem_univ (none))
  have hc0 : Q.coeff 0 = 0 := by rw [coeff_zero_eq_eval_zero, h0]
  have hnode : ∀ i : {i // i ∈ Γ}, Q.eval (point (p := p) i.val) = y i := by
    intro i
    exact Lagrange.eval_interpolate_at_node (r := r) hinj (Finset.mem_univ (some i))
  refine ⟨fun j => Q.coeff (j.val+1), ?_⟩
  funext i
  rw [← hnode i]
  simp only [L, eval_finsetSum, eval_monomial]
  rw [eval_eq_sum_range' hnd]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k-1, by omega⟩
  rw [Finset.sum_range_succ', hc0, zero_mul, add_zero,
    show m + 1 - 1 = m by omega, ← Fin.sum_univ_eq_sum_range (fun j => Q.coeff (j+1) * _ ^ (j+1))]

lemma fiber_card_gen {V W : Type*} [AddCommGroup V] [Fintype V] [AddCommGroup W] [Fintype W]
    [DecidableEq W] (f : V →+ W) (hf : Function.Surjective f) (w : W) :
    (Finset.univ.filter fun v => f v = w).card * Fintype.card W = Fintype.card V := by
  classical
  have hall : ∀ w', (Finset.univ.filter fun v => f v = w').card
      = (Finset.univ.filter fun v => f v = w).card := fun w' =>
    AddMonoidHom.card_fiber_eq_of_mem_range f (hf w') (hf w)
  have h := Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)
  rw [Finset.sum_congr rfl (fun w' _ => hall w'), Finset.sum_const, Finset.card_univ,
    Finset.card_univ, smul_eq_mul] at h
  rw [h, mul_comm]

lemma fiber_main {p n k : Nat} [Fact (Nat.Prime p)] (hk : 0 < k) (hnp : n < p)
    (Γ : Finset (Fin n)) (hΓ : Γ.card < k) (secret : ZMod p) (values : Observation p Γ)
    [DecidablePred fun coins : Coins p k => observe Γ secret coins = values] :
    (Finset.univ.filter fun coins : Coins p k => observe Γ secret coins = values).card
      = p ^ (k-1-Γ.card) := by
  classical
  have hset : (Finset.univ.filter fun coins : Coins p k => observe Γ secret coins = values)
      = Finset.univ.filter fun c => Lh p n k Γ c = values - fun _ => secret := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, observe_eq]
    constructor
    · rintro h; funext i; have := congrFun h i
      simp only [Pi.sub_apply, Lh, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this ⊢
      rw [← this]; ring
    · rintro h; funext i; have := congrFun h i
      simp only [Pi.sub_apply, Lh, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this ⊢
      rw [this]; ring
  have hmain := fiber_card_gen (Lh p n k Γ) (L_surj hk hnp Γ hΓ) (values - fun _ => secret)
  rw [← hset] at hmain
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_coe, Fintype.card_fin] at hmain
  have hp : 0 < p := (Fact.out : Nat.Prime p).pos
  have : p ^ (k-1) = p ^ (k-1-Γ.card) * p ^ Γ.card := by
    rw [← pow_add]; congr 1; omega
  rw [this] at hmain
  exact Nat.eq_of_mul_eq_mul_right (pow_pos hp _) hmain

end S108Sh
end

open Shamir1979
theorem solution (p n k : Nat) [Fact (Nat.Prime p)]
    (hk : 0 < k) (hkn : k ≤ n) (hnp : n < p)
    (Γ : Finset (Fin n)) (hΓ : Γ.card < k)
    (secret : ZMod p) (values : Observation p Γ) :
    fiberCount (k := k) Γ secret values = p ^ (k-1-Γ.card) := by
  classical
  unfold fiberCount
  convert S108Sh.fiber_main hk hnp Γ hΓ secret values
