-- Prove2me | solution 1 for FourierUncertainty.donoho_stark
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T08:00:16.659983+00:00
-- url     : https://prove2.me/submissions/4b0cfc7e-2a12-4fa6-857a-d2ff08ec7e8a

-- Sol generated from Bridges/FourierFunctorUncertainty.lean
import Mathlib
import Definitions.Def_Bridges_FourierFunctorUncertainty
import Theorems.Thm_FourierUncertainty_norm_dft_le

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
theorem solution(Φ : ZMod N → ℂ) (hΦ : Φ ≠ 0) :
    N ≤ (fsupport Φ).card * (fsupport (𝓕 Φ)).card := by
  classical
  obtain ⟨j₀, -, hj₀⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (ZMod N)) (fun j => ‖Φ j‖) ⟨0, mem_univ 0⟩
  set M : ℝ := ‖Φ j₀‖ with hMdef
  have hM : ∀ j, ‖Φ j‖ ≤ M := fun j => hj₀ j (mem_univ j)
  have hMpos : 0 < M := by
    rcases lt_or_eq_of_le (norm_nonneg (Φ j₀)) with h | h
    · exact h
    · exfalso
      apply hΦ
      funext j
      have : ‖Φ j‖ ≤ 0 := by rw [hMdef, ← h] at hM; exact hM j
      simpa using le_antisymm this (norm_nonneg _)
  -- bound on the Fourier side
  have h1 : ∀ k, ‖𝓕 Φ k‖ ≤ (fsupport Φ).card * M := norm_dft_le Φ M hM
  -- bound on the double transform
  have h2 : ‖𝓕 (𝓕 Φ) (-j₀)‖ ≤ (fsupport (𝓕 Φ)).card * ((fsupport Φ).card * M) :=
    norm_dft_le (𝓕 Φ) _ h1 (-j₀)
  have h3 : 𝓕 (𝓕 Φ) (-j₀) = (N : ℂ) • Φ j₀ := by
    have := congrFun (ZMod.dft_dft Φ) (-j₀)
    simpa using this
  rw [h3, norm_smul] at h2
  have h4 : (N : ℝ) * M ≤ (fsupport (𝓕 Φ)).card * ((fsupport Φ).card * M) := by
    simpa using h2
  have h6 : (N : ℝ) * M ≤ ((fsupport Φ).card * (fsupport (𝓕 Φ)).card : ℝ) * M := by
    nlinarith [h4]
  have h5 : (N : ℝ) ≤ (fsupport Φ).card * (fsupport (𝓕 Φ)).card :=
    le_of_mul_le_mul_right h6 hMpos
  exact_mod_cast h5
