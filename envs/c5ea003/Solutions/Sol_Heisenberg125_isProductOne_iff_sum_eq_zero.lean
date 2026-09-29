-- Prove2me | solution 1 for Heisenberg125.isProductOne_iff_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T19:17:55.179185+00:00
-- url     : https://prove2.me/submissions/1db5c305-cdc9-4f19-b91a-910764bc11fd

-- Sol generated from Algebra/Heisenberg125/AbelianDavenport.lean
import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
import Definitions.Def_Algebra_Heisenberg125_LowerBound
import Definitions.Def_Algebra_Heisenberg125_ZeroSumTwoDim
/-
# Exact small Davenport constants of the abelian sections of `H_{p^3}`

`H_{p^3}` sits in the extension `C_p → H_{p^3} → C_p ⊕ C_p`, and the two
abelian groups involved are exactly the ones controlling our bounds.  Here we
compute their small Davenport constants exactly:

* `smallDavenport_multiplicative_zmod : d(C_p) = p - 1`,
* `smallDavenport_multiplicative_zmod_sq : d(C_p ⊕ C_p) = 2p - 2`.

The upper bound for `C_p` is the general pigeonhole bound `d(G) ≤ |G| - 1`; the
upper bound for `C_p ⊕ C_p` is the Chevalley–Warning bound of
`Algebra.Heisenberg125.ZeroSumTwoDim`.  Both lower bounds are explicit
zero-sum-free sequences.

Consequently `d(H_{p^3}) ≥ 3p - 3 = d(C_p) + d(C_p ⊕ C_p)`, i.e. the
conjectural value `3p - 3` is exactly the sum of the Davenport constants of the
abelian sub- and quotient group — this is the structural reason behind the
conjecture of Godara and Sarkar.
-/

open Heisenberg125

open Multiplicative

variable {A : Type*} [AddCommGroup A]

/-- The product of a list in `Multiplicative A` is the sum of the list. -/
lemma toAdd_list_prod (L : List (Multiplicative A)) :
    toAdd L.prod = (L.map toAdd).sum := by
  induction L with
  | nil => rfl
  | cons g L ih => simp [ih]




/-! ## The cyclic group `C_p` -/

variable {p : ℕ}



/-! ## The group `C_p ⊕ C_p` -/




open Heisenberg125 in
theorem solution(L : List (Multiplicative A)) :
    IsProductOne L ↔ (L.map toAdd).sum = 0 := by
  constructor
  · rintro ⟨M, hM, hprod⟩
    have h1 : (M.map toAdd).sum = (L.map toAdd).sum := (hM.map _).sum_eq
    rw [← h1, ← toAdd_list_prod, hprod]
    rfl
  · intro h
    refine ⟨L, List.Perm.refl _, ?_⟩
    have := toAdd_list_prod L
    rw [h] at this
    exact toAdd.injective this
