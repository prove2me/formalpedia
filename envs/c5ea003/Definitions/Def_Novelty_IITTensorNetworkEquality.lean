-- Prove2me | Definitions.Def_Novelty_IITTensorNetworkEquality
-- name    : Novelty_IITTensorNetworkEquality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T15:52:13.074909+00:00
-- url     : https://prove2.me/theorems/ef4b8a82-5aa3-4560-9fb4-68d5a73fec2c
-- title:
--   Aether Catalog definitions — Novelty_IITTensorNetworkEquality
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.IITTensorNetworkEquality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/IITTensorNetworkEquality.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_IITTensorNetworkEntropy
import Definitions.Def_Novelty_IITTensorNetworkPhi
import Definitions.Def_Novelty_IITTensorNetworkSchmidt

/-! # Equality analysis for the entropy bounds of integrated information

The companion files prove the inequalities

* `sum_negMulLog_le_log_card_support` : `H(p) ≤ log |supp p|`;
* `vnEntropy_le_log_rank`             : `S(ρ) ≤ log (rank ρ)`;
* `mutualInformation_le_two_log_schmidtRank` : `I(A:B) ≤ 2 log (Schmidt rank)`;
* `phi_le_two_log_of_bondDim`         : `Φ ≤ 2 log χ`.

Here we settle the *equality cases*: each of these bounds is saturated exactly
when the relevant spectrum is **flat**, i.e. uniform on its support.  This is
the missing "only if" half of the saturation analysis, and it is what makes the
value `Φ(GHZ) = 2 log d` an extremal, not merely an example, computation.

Main results:

* `sum_negMulLog_eq_log_card_support_iff` : `H(p) = log |supp p|` iff `p` is
  uniform on its support;
* `vnEntropy_eq_log_rank_iff` : a density matrix saturates the maximal entropy
  bound iff its nonzero eigenvalues all equal `1 / rank`;
* `entanglementEntropy_eq_log_schmidtRank_iff` and
  `mutualInformation_eq_two_log_schmidtRank_iff` : the Schmidt-rank bound on the
  mutual information across a cut is saturated exactly at a flat Schmidt
  spectrum;
* `phi_lt_two_log_of_nonflat_cut` : if some cut of a chain state has a
  non-flat marginal spectrum, then `Φ` is *strictly* below the bound
  `2 log (Schmidt rank)` at that cut.

We also formalize the "product cut" mechanism behind reducibility:
`schmidtRank_eq_one_of_product` and `phi_eq_zero_of_product_cut` show that a
chain state which factorizes across one bipartition has `Φ = 0`, so integrated
information is destroyed by a single product cut no matter how entangled the
two blocks are internally.
-/

open Finset Matrix
open scoped ComplexOrder

namespace IITTensorNetwork

/-! ## Equality in the maximal entropy bound -/

section Shannon

variable {ι : Type*} [Fintype ι]






end Shannon

/-! ## Equality in the von Neumann bound -/

section VonNeumann

variable {m : Type*} [Fintype m] [DecidableEq m]




end VonNeumann

/-! ## Equality in the Schmidt-rank bound for mutual information -/

section Bipartite

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]




/-- The spectrum of the left marginal of a bipartite pure state is *flat* if all
its nonzero eigenvalues equal the reciprocal of the Schmidt rank. -/
def FlatSchmidtSpectrum (M : Matrix α β ℂ) : Prop :=
  ∀ i ∈ support (rhoLeft_posSemidef M).isHermitian.eigenvalues,
    (rhoLeft_posSemidef M).isHermitian.eigenvalues i = ((schmidtRank M : ℝ))⁻¹





end Bipartite


/-! ## Product cuts destroy integrated information -/

section ProductCut

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- A bipartite coefficient matrix is a *product across the cut* when it is the
outer product of a vector on the left part and a vector on the right part. -/
def ProductAcross (M : Matrix α β ℂ) : Prop :=
  ∃ (a : α → ℂ) (b : β → ℂ), M = Matrix.of fun i j => a i * b j




end ProductCut

/-! ## Consequences for the integrated information of a chain -/

section Chain

variable {n d : ℕ} {psi : (Fin n → Fin d) → ℂ}






end Chain

/-! ## Concatenation of two chains -/

section Concatenation

variable {n d : ℕ}

/-- The **concatenation** of a state of the first `l` sites with a state of the
remaining `n - l` sites: the two blocks are prepared independently. -/
noncomputable def concatState {l : ℕ} (hl : l ≤ n) (psiA : (Fin l → Fin d) → ℂ)
    (psiB : (Fin (n - l) → Fin d) → ℂ) : (Fin n → Fin d) → ℂ :=
  fun s => psiA (splitL l hl s) * psiB (splitR l hl s)




end Concatenation

end IITTensorNetwork


