-- Prove2me | solution 1 for RepresentativeFunctions.hasLinearRep_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T04:55:04.333727+00:00
-- url     : https://prove2.me/submissions/0eaffb11-fef1-4f9c-9d1e-005d627e86d4

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

@[simp] lemma mword_singleton {n : ℕ} (mu : X → Matrix (Fin n) (Fin n) K) (x : X) :
    mword mu [x] = mu x := by simp [mword]


/-! ## Linear representation ⟹ representative -/


/-! ## Representative ⟹ finite dimensional Hankel space -/


/-! ## Finite dimensional Hankel space ⟹ linear representation -/


/-! ## The Kleene–Schützenberger equivalence -/


/-! ## The algebra of representative functions -/







open RepresentativeFunctions in
theorem solution(f : List X → K)
    (hfin : FiniteDimensional K (transSpace f)) : HasLinearRep f := by
  set V := transSpace f with hV
  have hmem : ∀ w : List X, ltrans w f ∈ V := fun w => Submodule.subset_span ⟨w, rfl⟩
  have hstab : ∀ x : X, ∀ g ∈ V,
      (LinearMap.funLeft K K (fun u : List X => x :: u)) g ∈ V := by
    intro x
    have hmap : Submodule.map (LinearMap.funLeft K K (fun u : List X => x :: u)) V ≤ V := by
      rw [hV, transSpace, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨g, ⟨w, rfl⟩, rfl⟩
      have he : (LinearMap.funLeft K K (fun u : List X => x :: u)) (ltrans w f)
          = ltrans (w ++ [x]) f := by
        funext u; simp [LinearMap.funLeft_apply, ltrans]
      rw [he]
      exact Submodule.subset_span ⟨w ++ [x], rfl⟩
    intro g hg
    exact hmap ⟨g, hg, rfl⟩
  set n := Module.finrank K V with hn
  set b := Module.finBasis K V with hb
  set T : X → (V →ₗ[K] V) := fun x => (LinearMap.funLeft K K (fun u : List X => x :: u)).restrict
    (hstab x) with hT
  set mu : X → Matrix (Fin n) (Fin n) K := fun x => fun j i => b.repr (T x (b j)) i with hmu
  set lam : Fin n → K := fun i => b.repr ⟨ltrans [] f, hmem []⟩ i with hlam
  set gam : Fin n → K := fun i => (b i : List X → K) [] with hgam
  refine ⟨n, lam, mu, gam, ?_⟩
  have hrepr : ∀ (x : X) (v : V) (i : Fin n),
      b.repr (T x v) i = ∑ j, b.repr v j * mu x j i := by
    intro x v i
    have hv : T x v = ∑ j, b.repr v j • T x (b j) := by
      conv_lhs => rw [← b.sum_repr v]
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => map_smul _ _ _
    rw [hv, map_sum]
    simp [hmu]
  have hcoord : ∀ (w : List X) (i : Fin n),
      b.repr ⟨ltrans w f, hmem w⟩ i = ∑ k, lam k * mword mu w k i := by
    intro w
    induction w using List.reverseRecOn with
    | nil => intro i; simp [mword, Matrix.one_apply, hlam]
    | append_singleton w x ih =>
      intro i
      have hstep : (⟨ltrans (w ++ [x]) f, hmem (w ++ [x])⟩ : V) = T x ⟨ltrans w f, hmem w⟩ := by
        apply Subtype.ext
        funext u
        simp [hT, LinearMap.restrict_apply, LinearMap.funLeft_apply, ltrans]
      rw [hstep, hrepr]
      simp only [ih]
      rw [mword_append, mword_singleton]
      simp only [Matrix.mul_apply]
      have hL : ∑ j, (∑ k, lam k * mword mu w k j) * mu x j i
          = ∑ j, ∑ k, lam k * mword mu w k j * mu x j i :=
        Finset.sum_congr rfl fun j _ => Finset.sum_mul _ _ _
      rw [hL, Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  intro w
  have hsum : (⟨ltrans w f, hmem w⟩ : V) = ∑ i, b.repr ⟨ltrans w f, hmem w⟩ i • b i :=
    (b.sum_repr _).symm
  have hval : f w = ∑ i, b.repr ⟨ltrans w f, hmem w⟩ i * gam i := by
    have hc := congrArg (fun v : V => (v : List X → K) []) hsum
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hc
    have h2 : (ltrans w f) [] = f w := by simp [ltrans]
    rw [← h2, hc]
    simp [hgam, Finset.sum_apply]
  rw [hval]
  calc ∑ i, b.repr (⟨ltrans w f, hmem w⟩ : V) i * gam i
      = ∑ i, ∑ k, lam k * mword mu w k i * gam i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hcoord w i, Finset.sum_mul]
    _ = ∑ k, ∑ i, lam k * mword mu w k i * gam i := Finset.sum_comm
