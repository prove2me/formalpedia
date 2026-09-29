-- Prove2me | Theorems.Thm_FiniteAbelianUncertainty_norm_weighted_sum_le
-- name    : FiniteAbelianUncertainty.norm_weighted_sum_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:47:18.147133+00:00
-- url     : https://prove2.me/theorems/b1d7b00c-a46c-462f-9483-d2ddf0eba9d7
-- title:
--   A weighted sum with unimodular weights, supported on a finite set, is bounded by the size of
-- statement:
--   A weighted sum with unimodular weights, supported on a finite set, is bounded by the size of
--   that set times the sup bound. This is the only analytic input of the uncertainty principle.
--
--   ```lean
--   theorem FiniteAbelianUncertainty.norm_weighted_sum_le{I : Type*} [Fintype I] (w g : I → ℂ) (K : ℝ)
--       (hw : ∀ i, ‖w i‖ ≤ 1) (hK : ∀ i, ‖g i‖ ≤ K) (S : Finset I) (hS : ∀ i, i ∉ S → g i = 0) :
--       ‖∑ i, w i * g i‖ ≤ S.card * K := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/FiniteAbelianUncertainty.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/FiniteAbelianUncertainty.lean#L51

-- Thm stub generated from Bridges/FiniteAbelianUncertainty.lean
import Mathlib
import Definitions.Def_Bridges_FiniteAbelianUncertainty
import Definitions.Def_Bridges_FourierFunctorUncertainty

/-!
# Donoho–Stark uncertainty for arbitrary finite abelian groups

`Catalog/Bridges/FourierFunctorUncertainty.lean` proved the Donoho–Stark uncertainty principle on
`ZMod N`, where the characters are explicit roots of unity. This file shows the argument is
structural rather than cyclic: it needs only that characters have modulus one and that the
character-sum inversion formula holds. We therefore obtain the uncertainty principle for an
arbitrary finite abelian group `G`, with the Fourier transform taking values on the Pontryagin
dual `AddChar G ℂ`.

## Main results

* `FiniteAbelianUncertainty.gdft_inversion` : the character-sum inversion formula
  `∑_ψ ψ b · 𝓖f(ψ) = |G| · f b`.
* `FiniteAbelianUncertainty.donoho_stark_finite_abelian` : for every nonzero `f : G → ℂ`,
  `|G| ≤ |supp f| * |supp 𝓖f|`, the support on the right being taken in the dual group.
* `FiniteAbelianUncertainty.donoho_stark_sharp_delta` : the bound is attained by delta functions,
  so it is sharp for every finite abelian group.
-/

open Finset AddChar

open FiniteAbelianUncertainty

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem FiniteAbelianUncertainty.norm_weighted_sum_le{I : Type*} [Fintype I] (w g : I → ℂ) (K : ℝ)
    (hw : ∀ i, ‖w i‖ ≤ 1) (hK : ∀ i, ‖g i‖ ≤ K) (S : Finset I) (hS : ∀ i, i ∉ S → g i = 0) :
    ‖∑ i, w i * g i‖ ≤ S.card * K := by sorry
