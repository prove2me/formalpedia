-- Prove2me | Definitions.Def_Shared_FourierSubgroupDuality
-- name    : Shared_FourierSubgroupDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:35:54.176819+00:00
-- url     : https://prove2.me/theorems/eae150f1-aba3-432b-bb34-8d2df7caa60b
-- title:
--   Aether Catalog definitions — Shared_FourierSubgroupDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.FourierSubgroupDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/FourierSubgroupDuality.lean by skeleton subtraction
import Mathlib
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

namespace FourierFA

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
  (H : AddSubgroup G) [DecidablePred (· ∈ H)]

/-- The underlying finset of a subgroup. -/
def subFinset : Finset G := Finset.univ.filter (· ∈ H)

/-- The indicator function of a subgroup. -/
noncomputable def indic : G → ℂ := fun x => if x ∈ H then 1 else 0

/-- The annihilator (orthogonal complement) of `H` inside the dual group. -/
noncomputable def annih : Finset (AddChar G ℂ) :=
  Finset.univ.filter (fun ψ : AddChar G ℂ => ∀ x ∈ H, ψ x = 1)

variable {H}












end FourierFA


