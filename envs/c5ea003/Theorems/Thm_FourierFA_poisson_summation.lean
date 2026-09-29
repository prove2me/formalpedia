-- Prove2me | Theorems.Thm_FourierFA_poisson_summation
-- name    : FourierFA.poisson_summation
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:35:52.480983+00:00
-- url     : https://prove2.me/theorems/d9a9e5eb-abb5-4483-8ceb-f0fe80c29365
-- title:
--   Poisson summation for a subgroup `H â¤ G`:
-- statement:
--   **Poisson summation** for a subgroup `H â¤ G`:
--   `|G| * â_{x â H} f x = |H| * â_{Ï â H^â¥} fÌ Ï`.
--
--   ```lean
--   theorem FourierFA.poisson_summation(f : G → ℂ) :
--       (Fintype.card G : ℂ) * ∑ x ∈ subFinset H, f x
--         = ((subFinset H).card : ℂ) * ∑ ψ ∈ annih H, dft f ψ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/FourierSubgroupDuality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/FourierSubgroupDuality.lean#L179

-- Thm stub generated from Shared/FourierSubgroupDuality.lean
import Mathlib
import Definitions.Def_Shared_FourierFiniteAbelian
import Definitions.Def_Shared_FourierSubgroupDuality
/-
# Subgroups, annihilators and extremals of the uncertainty principle

Building on `Catalog.Shared.FourierFiniteAbelian`, this file studies the Fourier transform of
the indicator function of a subgroup `H ≤ G` of a finite abelian group.

Main results:

* `FourierFA.sum_char_over_subgroup` : `∑_{x ∈ H} ψ x = |H| ⬝ [ψ ∈ H^⊥]`.
* `FourierFA.dft_indic` : the Fourier transform of `1_H` is `|H| ⬝ 1_{H^⊥}`.
* `FourierFA.card_subgroup_mul_card_annihilator` : `|H| * |H^⊥| = |G|`, obtained *from Plancherel*
  rather than from Pontryagin duality of the quotient.
* `FourierFA.uncertainty_eq_subgroup` : subgroup indicators are extremal for the Donoho–Stark
  uncertainty principle, i.e. `|supp 1_H| * |supp (1_H)^| = |G|` exactly.
* `FourierFA.poisson_summation` : `|G| * ∑_{x ∈ H} f x = |H| * ∑_{ψ ∈ H^⊥} f̂ ψ`.
-/


open Finset Fintype ComplexConjugate

open FourierFA

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  (H : AddSubgroup G) [DecidablePred (· ∈ H)]




variable {H}

theorem FourierFA.poisson_summation(f : G → ℂ) :
    (Fintype.card G : ℂ) * ∑ x ∈ subFinset H, f x
      = ((subFinset H).card : ℂ) * ∑ ψ ∈ annih H, dft f ψ := by sorry
