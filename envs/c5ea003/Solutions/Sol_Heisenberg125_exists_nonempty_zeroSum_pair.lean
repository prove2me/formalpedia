-- Prove2me | solution 1 for Heisenberg125.exists_nonempty_zeroSum_pair
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:12:31.914821+00:00
-- url     : https://prove2.me/submissions/b07e7d6c-0808-4ce4-b943-53dc843e51c2

-- Sol generated from Algebra/Heisenberg125/ZeroSumTwoDim.lean
import Mathlib
import Definitions.Def_Algebra_Heisenberg125_ZeroSumTwoDim
/-
# The Davenport constant of `(ZMod p)^2`: `D(C_p ⊕ C_p) ≤ 2p - 1`

This file proves, by an application of the **Chevalley–Warning theorem**, that
any sequence of `2p - 1` vectors in `(ZMod p)^2` admits a nonempty subsequence
summing to zero (`exists_nonempty_zeroSum_sublist`).

This is the additive-combinatorial engine behind the "line bound" of
`Algebra.Heisenberg125.LineBound`: the preimage in `H_{p^3}` of a line through
the origin of `(ZMod p)^2` is an abelian subgroup isomorphic to `C_p ⊕ C_p`, and
product-one-freeness there is exactly zero-sum-freeness in `(ZMod p)^2`.

The Finset version `exists_nonempty_zeroSum_pair` is stated for two coordinate
functions `u, w : Fin n → ZMod p` so that it can be applied directly to
arbitrary pairs of `ZMod p`-valued statistics of a sequence.
-/

open Heisenberg125

open Finset MvPolynomial

variable {p : ℕ} [Fact p.Prime]


/-- The Chevalley–Warning test polynomial `Σ_i u i • X i ^ (p - 1)`. -/
private noncomputable def cwPoly {n : ℕ} (u : Fin n → ZMod p) : MvPolynomial (Fin n) (ZMod p) :=
  ∑ i, u i • X i ^ (p - 1)

private lemma totalDegree_cwPoly_le {n : ℕ} (u : Fin n → ZMod p) :
    (cwPoly u).totalDegree ≤ p - 1 := by
  refine totalDegree_finsetSum_le ?_
  rintro i -
  exact (totalDegree_smul_le _ _).trans (totalDegree_X_pow _ _).le

private lemma eval_cwPoly {n : ℕ} (u : Fin n → ZMod p) (x : Fin n → ZMod p) :
    eval x (cwPoly u) = ∑ i ∈ Finset.univ.filter (fun i => x i ≠ 0), u i := by
  classical
  rw [cwPoly, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.smul_eval, map_pow, eval_X, ZMod.pow_card_sub_one]
  by_cases h : x i = 0 <;> simp [h]






open Heisenberg125 in
theorem solution{n : ℕ} (u w : Fin n → ZMod p) (hn : 2 * p - 1 ≤ n) :
    ∃ t : Finset (Fin n), t.Nonempty ∧ ∑ i ∈ t, u i = 0 ∧ ∑ i ∈ t, w i = 0 := by
  classical
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  set N := Fintype.card {x : Fin n → ZMod p // eval x (cwPoly u) = 0 ∧ eval x (cwPoly w) = 0}
    with hN
  have hzero : eval (0 : Fin n → ZMod p) (cwPoly u) = 0 ∧
      eval (0 : Fin n → ZMod p) (cwPoly w) = 0 := by
    constructor <;>
      · rw [eval_cwPoly]
        apply Finset.sum_eq_zero
        intro i hi
        simp at hi
  have hN₀ : 0 < N := @Fintype.card_pos _ _ ⟨⟨0, hzero⟩⟩
  have hdeg : (cwPoly u).totalDegree + (cwPoly w).totalDegree < Fintype.card (Fin n) := by
    have h1 := totalDegree_cwPoly_le u
    have h2 := totalDegree_cwPoly_le w
    simp only [Fintype.card_fin]
    omega
  have hpN : p ∣ N := char_dvd_card_solutions_of_add_lt p hdeg
  obtain ⟨x, hx⟩ := Fintype.exists_ne_of_one_lt_card
    ((Fact.out : p.Prime).one_lt.trans_le (Nat.le_of_dvd hN₀ hpN)) ⟨0, hzero⟩
  refine ⟨Finset.univ.filter (fun i => x.1 i ≠ 0), ?_, ?_, ?_⟩
  · rw [← Subtype.coe_ne_coe, Function.ne_iff] at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, by simpa using hi⟩
  · rw [← eval_cwPoly]; exact x.2.1
  · rw [← eval_cwPoly]; exact x.2.2
