-- Prove2me | solution 1 for RepresentativeFunctions.isRepresentative_of_hasLinearRep
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:55:04.882749+00:00
-- url     : https://prove2.me/submissions/b77fdc6a-5f44-46e0-8d22-258ebc571e1a

-- Sol generated from Novelty/RepresentativeFunctions.lean
import Mathlib
import Definitions.Def_Novelty_RepresentativeFunctions
/-
# Representative functions on a free monoid and the Kleene–Schützenberger theorem

Following *Various bialgebras of representative functions on free monoids*, a function
`f : X* → K` is **representative** when its "coproduct" factors through a finite tensor:
`f(uv) = Σ_{i<n} g_i(u) h_i(v)`.  Its **graph** is the noncommutative series
`Σ_w f(w) w`, and the Kleene–Schützenberger theorem identifies representative functions
with the series admitting a **linear representation** `f(w) = λ μ(w) γ`, where
`μ : X* → M_n(K)` is a monoid morphism.

This file proves the full equivalence, in the form of a three-way cycle:

* `IsRepresentative f → FiniteDimensional K (transSpace f)`
  (`finiteDimensional_transSpace_of_isRepresentative`);
* `FiniteDimensional K (transSpace f) → HasLinearRep f`
  (`hasLinearRep_of_finiteDimensional`) — the Myhill–Nerode / Hankel-rank construction:
  the space spanned by the left translates of `f` is stable under the shift operators,
  and reading these operators in a basis produces the representation;
* `HasLinearRep f → IsRepresentative f` (`isRepresentative_of_hasLinearRep`).

The resulting `tfae` statement `representative_tfae` is the Kleene–Schützenberger
equivalence in the "representative function" formulation used by the paper.

We also prove the closure properties which make the representative functions a
subalgebra of `K^{X*}`: they are closed under scalar multiples, sums and the Hadamard
(pointwise) product, the latter through the tensor product of linear representations.
-/

open RepresentativeFunctions

variable {X K : Type*} [Field K]

/-! ## Translates -/




/-! ## Representative functions and linear representations -/




lemma mword_append {n : ℕ} (mu : X → Matrix (Fin n) (Fin n) K) (u v : List X) :
    mword mu (u ++ v) = mword mu u * mword mu v := by
  induction u with
  | nil => simp [mword]
  | cons a u ih => simp [mword, ih, mul_assoc]



/-! ## Linear representation ⟹ representative -/


/-! ## Representative ⟹ finite dimensional Hankel space -/


/-! ## Finite dimensional Hankel space ⟹ linear representation -/


/-! ## The Kleene–Schützenberger equivalence -/


/-! ## The algebra of representative functions -/







open RepresentativeFunctions in
theorem solution{f : List X → K} (hf : HasLinearRep f) :
    IsRepresentative f := by
  obtain ⟨n, lam, mu, gam, hrep⟩ := hf
  refine ⟨n, fun k u => ∑ i, lam i * mword mu u i k, fun k v => ∑ j, mword mu v k j * gam j,
    fun u v => ?_⟩
  rw [hrep (u ++ v)]
  have expand : ∀ i j : Fin n, lam i * mword mu (u ++ v) i j * gam j
      = ∑ k, lam i * mword mu u i k * (mword mu v k j * gam j) := by
    intro i j
    rw [mword_append, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  calc ∑ i, ∑ j, lam i * mword mu (u ++ v) i j * gam j
      = ∑ i, ∑ j, ∑ k, lam i * mword mu u i k * (mword mu v k j * gam j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => expand i j
    _ = ∑ i, ∑ k, ∑ j, lam i * mword mu u i k * (mword mu v k j * gam j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, lam i * mword mu u i k * (mword mu v k j * gam j) := Finset.sum_comm
    _ = ∑ k, (∑ i, lam i * mword mu u i k) * ∑ j, mword mu v k j * gam j := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm
