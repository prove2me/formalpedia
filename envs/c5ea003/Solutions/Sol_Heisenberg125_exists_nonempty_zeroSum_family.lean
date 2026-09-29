-- Prove2me | solution 1 for Heisenberg125.exists_nonempty_zeroSum_family
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T14:12:31.373722+00:00
-- url     : https://prove2.me/submissions/01e90779-36bf-4d1f-a3c7-af305727abdd

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

-- cwPoly is declared `private` in Def_Algebra_Heisenberg125_ZeroSumTwoDim, so it
-- is not accessible here; redefine it locally for this solution file.
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
set_option maxHeartbeats 1000000 in
theorem solution{ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (u : ι → Fin n → ZMod p) (hn : Fintype.card ι * (p - 1) < n) :
    ∃ t : Finset (Fin n), t.Nonempty ∧ ∀ j, ∑ i ∈ t, u j i = 0 := by
  set F : ι → MvPolynomial (Fin n) (ZMod p) := fun j => cwPoly (u j) with hF
  letI : ∀ x : Fin n → ZMod p,
      Decidable (∀ i ∈ (Finset.univ : Finset ι), eval x (F i) = 0) :=
    fun _ => decidableDforallFinset
  have hzero : ∀ j ∈ (Finset.univ : Finset ι), eval (0 : Fin n → ZMod p) (F j) = 0 := by
    intro j _
    rw [hF, eval_cwPoly]
    exact Finset.sum_eq_zero (by intro i hi; simp at hi)
  have hdeg : ∑ j : ι, (F j).totalDegree < Fintype.card (Fin n) := by
    calc ∑ j : ι, (F j).totalDegree ≤ ∑ _j : ι, (p - 1) :=
          Finset.sum_le_sum fun j _ => totalDegree_cwPoly_le (u j)
      _ = Fintype.card ι * (p - 1) := by simp
      _ < Fintype.card (Fin n) := by simpa using hn
  have hpN := char_dvd_card_solutions_of_sum_lt (K := ZMod p) p
    (s := (Finset.univ : Finset ι)) (f := F) hdeg
  obtain ⟨x, hx⟩ := Fintype.exists_ne_of_one_lt_card
    ((Fact.out : p.Prime).one_lt.trans_le
      (Nat.le_of_dvd (Fintype.card_pos_iff.2 ⟨⟨0, hzero⟩⟩) hpN)) ⟨0, hzero⟩
  refine ⟨Finset.univ.filter (fun i => x.1 i ≠ 0), ?_, ?_⟩
  · rw [← Subtype.coe_ne_coe, Function.ne_iff] at hx
    obtain ⟨i, hi⟩ := hx
    exact ⟨i, by simpa using hi⟩
  · intro j
    rw [← eval_cwPoly]
    exact x.2 j (Finset.mem_univ j)
