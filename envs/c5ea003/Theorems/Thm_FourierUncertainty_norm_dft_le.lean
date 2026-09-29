-- Prove2me | Theorems.Thm_FourierUncertainty_norm_dft_le
-- name    : FourierUncertainty.norm_dft_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:42:50.884733+00:00
-- url     : https://prove2.me/theorems/1619c2c8-ec01-49b3-84cb-b10ec3c298f6
-- title:
--   Every Fourier coefficient is bounded by the size of the support times the sup norm.
-- statement:
--   Every Fourier coefficient is bounded by the size of the support times the sup norm.
--
--   ```lean
--   theorem FourierUncertainty.norm_dft_le(Φ : ZMod N → ℂ) (M : ℝ) (hM : ∀ j, ‖Φ j‖ ≤ M) (k : ZMod N) :
--       ‖𝓕 Φ k‖ ≤ (fsupport Φ).card * M := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/FourierFunctorUncertainty.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/FourierFunctorUncertainty.lean#L149

-- Thm stub generated from Bridges/FourierFunctorUncertainty.lean
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

theorem FourierUncertainty.norm_dft_le(Φ : ZMod N → ℂ) (M : ℝ) (hM : ∀ j, ‖Φ j‖ ≤ M) (k : ZMod N) :
    ‖𝓕 Φ k‖ ≤ (fsupport Φ).card * M := by sorry
