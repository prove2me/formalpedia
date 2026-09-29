-- Prove2me | solution 1 for FourierUncertainty.card_dft_zeros_le_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T08:00:15.514983+00:00
-- url     : https://prove2.me/submissions/0200da7e-de36-4c43-8ec5-fa3849d5ad63

-- Sol generated from Bridges/FourierFunctorUncertainty.lean
import Mathlib
import Definitions.Def_Bridges_FourierFunctorUncertainty

/-!
# Fourier as a functor, cycle 1: correct naturality domain and a genuine uncertainty principle

This file continues `Catalog/Bridges/FourierAsFunctor.lean`. That file established a
finite-coordinate categorical model of character duality and proved two *negative* results:

* the discrete Fourier matrices are **not** a natural endomorphism of the identity functor on a
  category whose arrows are all linear maps, and
* contravariant duality alone does **not** force any support uncertainty bound.

Both negative results are answered here positively, with substantive hypotheses.

## Main results

* `FourierUncertainty.dftNatIso` : the discrete Fourier transform on `ZMod N` **is** a natural
  isomorphism once the arrows are restricted to the multiplicative-unit automorphisms of
  `ZMod N`, i.e. between the pullback representation functor and its inverse twist, both viewed
  as functors `SingleObj (ZMod N)ˣ ⥤ ModuleCat ℂ`. This identifies the correct naturality domain.
* `FourierUncertainty.donoho_stark` : the Donoho–Stark uncertainty principle
  `N ≤ |supp Φ| * |supp (𝓕 Φ)|` for every nonzero `Φ : ZMod N → ℂ`. This is the substantive
  replacement for the disproved "contravariance implies uncertainty" claim.
* `FourierUncertainty.donoho_stark_sharp` : the bound is attained exactly, by delta functions.
* `FourierUncertainty.donoho_stark_am_gm` : the additive form `4 * N ≤ (|supp Φ| + |supp 𝓕Φ|)^2`.
* `FourierUncertainty.dualMap_comp` and `FourierUncertainty.doubleDualEmb_natural` : arrow-level
  functoriality of the character dual and naturality of the biduality evaluation map, together
  with `doubleDualEquiv_natural`, the natural-isomorphism form for finite abelian groups.
-/

open CategoryTheory Finset ZMod AddChar

open FourierUncertainty

/-! ## 1. The correct naturality domain for the discrete Fourier transform -/


variable {N : ℕ} [NeZero N]













/-! ## 2. The Donoho–Stark uncertainty principle -/


variable {N : ℕ} [NeZero N]




/-- A function supported in `{a, b}` has a two-term Fourier transform. -/
theorem dft_of_support_pair {Φ : ZMod N → ℂ} {a b : ZMod N} (hab : a ≠ b)
    (hsub : ∀ j, j ≠ a → j ≠ b → Φ j = 0) (k : ZMod N) :
    𝓕 Φ k = stdAddChar (-(a * k)) * Φ a + stdAddChar (-(b * k)) * Φ b := by
  rw [ZMod.dft_apply]
  have hsum : ∑ j : ZMod N, stdAddChar (-(j * k)) • Φ j
      = ∑ j ∈ ({a, b} : Finset (ZMod N)), stdAddChar (-(j * k)) • Φ j := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    simp [hsub x hx.1 hx.2]
  rw [hsum, Finset.sum_pair hab]
  simp [smul_eq_mul]










/-! ## 3. Arrow-level biduality: functoriality and naturality of the evaluation map -/


variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]







variable [Finite A] [Finite B]







/-! ## 4. A prime refinement: Tao's `|supp Φ| + |supp 𝓕Φ| ≥ p + 1` for two-element supports

Donoho–Stark is sharp in general, but for prime modulus Tao's uncertainty principle gives the
strictly stronger additive bound `|supp Φ| + |supp 𝓕Φ| ≥ p + 1`. We prove this bound
unconditionally in the two-element-support case, where it is equivalent to the statement that a
nonzero two-term exponential sum vanishes at most once. -/


open scoped Classical

variable {p : ℕ} [Fact p.Prime] {Φ : ZMod p → ℂ} {a b : ZMod p}








/-! ## 5. Primality is essential: a composite counterexample to the Tao bound

For `N = 4` the indicator function of the subgroup `{0, 2}` is a fixed point of the Fourier
transform up to scale: both it and its transform have support of size two. Hence the additive
bound `|supp Φ| + |supp 𝓕Φ| ≥ N + 1` **fails** for composite modulus, while Donoho–Stark
`|supp Φ| * |supp 𝓕Φ| ≥ N` holds with equality. So the extremals of the multiplicative bound are
not only delta functions: subgroup indicators are extremal too. -/


open scoped Classical

















open FourierUncertainty in
theorem solution(hab : a ≠ b) (ha : Φ a ≠ 0)
    (hsub : ∀ j, j ≠ a → j ≠ b → Φ j = 0) :
    ((Finset.univ.filter fun k => 𝓕 Φ k = 0) : Finset (ZMod p)).card ≤ 1 := by
  refine Finset.card_le_one.2 fun k₁ h₁ k₂ h₂ => ?_
  simp only [Finset.mem_filter] at h₁ h₂
  -- from vanishing at `k` we read off the value of the character at `(b - a) * k`
  have key : ∀ k : ZMod p, 𝓕 Φ k = 0 → stdAddChar ((b - a) * k) * Φ a = -Φ b := by
    intro k hk
    have hsplit : stdAddChar (-(a * k)) = stdAddChar (-(b * k)) * stdAddChar ((b - a) * k) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    rw [dft_of_support_pair hab hsub k, hsplit] at hk
    have hne : (stdAddChar (-(b * k)) : ℂ) ≠ 0 := by
      intro h
      have : ‖stdAddChar (-(b * k))‖ = 1 := AddChar.norm_apply _ _
      rw [h] at this
      simp at this
    have : stdAddChar (-(b * k)) * (stdAddChar ((b - a) * k) * Φ a + Φ b) = 0 := by
      rw [← hk]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hne
    · linear_combination h
  have e1 := key k₁ h₁.2
  have e2 := key k₂ h₂.2
  have hchar : stdAddChar ((b - a) * k₁) = stdAddChar ((b - a) * k₂) := by
    have : stdAddChar ((b - a) * k₁) * Φ a = stdAddChar ((b - a) * k₂) * Φ a := by
      rw [e1, e2]
    exact mul_right_cancel₀ ha this
  have harg : (b - a) * k₁ = (b - a) * k₂ := ZMod.injective_stdAddChar hchar
  have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  exact mul_left_cancel₀ hba harg
