-- Prove2me | Theorems.Thm_FourierAdd_norm_error_lt
-- name    : FourierAdd.norm_error_lt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:34:07.60209+00:00
-- url     : https://prove2.me/theorems/c3dd2388-057f-44ec-9ba4-fd3dac635996
-- title:
--   Under the CauchyâSchwarz condition, the nonprincipal contribution is strictly smaller than
-- statement:
--   Under the CauchyâSchwarz condition, the nonprincipal contribution is strictly smaller than
--   the main term `|A| * |B|`.
--
--   ```lean
--   theorem FourierAdd.norm_error_lt(A B : Finset G) (c : G)
--       (h : ((Fintype.card G : ℝ) - A.card) * ((Fintype.card G : ℝ) - B.card)
--         < (A.card : ℝ) * (B.card : ℝ)) :
--       ‖∑ ψ ∈ (Finset.univ : Finset (AddChar G ℂ)).erase 0,
--           ψ c * (dft (indF A) ψ * dft (indF B) ψ)‖ < (A.card : ℝ) * (B.card : ℝ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/FourierAdditive.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/FourierAdditive.lean#L137

-- Thm stub generated from Shared/FourierAdditive.lean
import Mathlib
import Definitions.Def_Shared_FourierAdditive
import Definitions.Def_Shared_FourierFiniteAbelian
/-
# A Fourier-analytic sumset theorem on finite abelian groups

Building on `Catalog.Shared.FourierFiniteAbelian`, this file uses the convolution theorem,
Fourier inversion, Parseval's identity and Cauchy–Schwarz to count representations
`c = a + b` with `a ∈ A`, `b ∈ B` in a finite abelian group `G`.

Main results:

* `FourierAdd.conv_indF` : the convolution of two indicators counts representations.
* `FourierAdd.card_mul_rep_eq` : the Fourier counting formula
  `|G| * r_{A,B}(c) = ∑_ψ ψ(c) · 1̂_A(ψ) · 1̂_B(ψ)`.
* `FourierAdd.norm_error_lt` : the nonprincipal characters contribute strictly less than
  `|A| * |B|` when `(|G| - |A|)(|G| - |B|) < |A||B|`.
* `FourierAdd.exists_add_eq` : consequently `A + B = G`.  The hypothesis turns out to be
  *equivalent* to the pigeonhole bound `|A| + |B| > |G|` (see `cardCondition_iff`), so the
  Fourier/Cauchy–Schwarz route reproduces exactly the pigeonhole threshold — Cauchy–Schwarz is
  tight here.
* `FourierAdd.exists_add_eq_of_card_add_card_gt` : the classical pigeonhole corollary.
* `FourierAdd.cardCondition_iff` : the Cauchy–Schwarz hypothesis is *exactly equivalent* to
  `|A| + |B| > |G|`; so the Fourier route recovers, and does not beat, the pigeonhole threshold.
* `FourierAdd.energy_identity` : the exact Plancherel/additive-energy identity
  `|G| * ∑_c r(c)² = (|A||B|)² + ∑_{ψ ≠ 0} |1̂_A(ψ)|² |1̂_B(ψ)|²`.
* `FourierAdd.card_support_rep_ge` : the resulting quantitative covering bound
  `|{c : r(c) > 0}| ≥ |G| (|A||B|)² / ((|A||B|)² + E)`.
-/


open Finset ComplexConjugate FourierFA

open FourierAdd

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem FourierAdd.norm_error_lt(A B : Finset G) (c : G)
    (h : ((Fintype.card G : ℝ) - A.card) * ((Fintype.card G : ℝ) - B.card)
      < (A.card : ℝ) * (B.card : ℝ)) :
    ‖∑ ψ ∈ (Finset.univ : Finset (AddChar G ℂ)).erase 0,
        ψ c * (dft (indF A) ψ * dft (indF B) ψ)‖ < (A.card : ℝ) * (B.card : ℝ) := by sorry
