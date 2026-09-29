-- Prove2me | Definitions.Def_Novelty_CutIndexedTensorNetwork
-- name    : Novelty_CutIndexedTensorNetwork
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T15:50:46.470419+00:00
-- url     : https://prove2.me/theorems/7aaf97d9-61b8-4c57-81a2-d642397445a2
-- title:
--   Aether Catalog definitions — Novelty_CutIndexedTensorNetwork
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.CutIndexedTensorNetwork`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/CutIndexedTensorNetwork.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_CutIndexedEntropy
import Definitions.Def_Novelty_CutIndexedSingleton
import Definitions.Def_Novelty_IITTensorNetworkMPS

/-!
# Cut-indexed defects III: the quantum code state and its cut entropies

Files I and II developed the *classical* cut data of a codebook: the bond
dimension `cutRank C S` across a cut, the cut-wise Singleton inequality, and the
Shannon entropy `cutEntropy C S` of the induced marginal.  This file promotes the
codebook to a **quantum state** — the uniform superposition
`|C⟩ = |C|^(-1/2) ∑_{c ∈ C} |c⟩` — presented, for each cut `S`, as the coefficient
matrix `codeState C S` of a bipartite pure state in the sense of
`Catalog/Novelty/IITTensorNetworkSchmidt.lean`.

The point of the exercise is that the *tensor-network* cut data of `|C⟩` (Schmidt
rank, bond dimension, entanglement entropy) is controlled by, and for MDS codes
computed exactly by, the *combinatorial* cut data of `C`.

## Main results

* `normalized_codeState` : `|C⟩` is a unit vector, for every cut;
* `hasBondDim_codeState` : the code state factors through a virtual space of
  dimension `cutRank C S`, i.e. it is an MPS bond of that size;
* `schmidtRank_codeState_le` : hence `Schmidt rank ≤ cutRank C S`;
* `schmidtRank_codeState_le_pow_compl` : the complementary (purity) bound
  `Schmidt rank ≤ q ^ |Sᶜ|`;
* `entanglementEntropy_codeState_le_min` : **quantum cut-wise Singleton.**  For a
  code of minimum distance `d`, the entanglement entropy of `|C⟩` across any cut
  obeys `E(S) ≤ min (|S|, n + 1 - d) * log q`, the same plateau curve that bounds
  the classical cut entropy;
* `rhoLeft_codeState_of_isMDS` : for an MDS code and a cut of size at most
  `min (k, d - 1)`, the reduced density matrix is *exactly* maximally mixed;
* `entanglementEntropy_codeState_of_isMDS` : consequently
  `E(S) = |S| * log q` — **the quantum cut-wise Singleton inequality is saturated
  by MDS code states in the whole regime `|S| ≤ min (k, d-1)`**;
* `schmidtRank_codeState_of_isMDS` : the Schmidt rank across such a cut is exactly
  `q ^ |S|`, i.e. the bond-dimension bound `schmidtRank ≤ cutRank` is attained;
* `entanglementEntropy_codeState_eq_log_schmidtRank` : the entropy–Schmidt-rank
  bound of `IITTensorNetworkSchmidt.lean` is *saturated* by MDS code states;
* `mutualInformation_codeState_of_isMDS` : the quantum mutual information across
  such a cut lies between `|S| log q` and `2 |S| log q`, the extreme values allowed
  by `IITTensorNetwork.mutualInformation_le_two_log_schmidtRank`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the classical cut-wise Singleton inequality should have
a verbatim quantum avatar for the uniform code state, and MDS codes should be
exactly the states that saturate it — a discrete analogue of "maximal entanglement
up to the RT surface".

Experiment (Experimenter): the bound direction is cheap once the code state is
factored through the set of realised patterns
(`hasBondDim_codeState`, via `Finset.equivFin` on the image), because Schmidt rank
is then bounded by `cutRank C S`, which files I–II already bound by
`min (|S|, k)` in the exponent.  The saturation direction required computing
`ρ_A = M Mᴴ` entrywise: off-diagonal entries `(a, a')` count codewords that agree
off `S`, and minimum distance kills them as soon as `|S| ≤ d - 1`; the diagonal
entries are the balanced fibre counts of `fiber_card_of_isMDS`.  The result is
`ρ_A = q^(-|S|) • 1`, whose von Neumann entropy is `|S| log q` by
`IITTensorNetwork.vnEntropy_smul_one`.

Analysis (Analyst): the two saturation regimes differ, and this is not an artefact:
classically the entropy plateau reaches `k log q`, quantum-mechanically the purity
of `|C⟩` forces `E(S) = E(Sᶜ) ≤ min(|S|, |Sᶜ|) log q`, so exact saturation can only
be expected for `|S| ≤ d - 1` (where the complement still resolves the code).  The
theorem is stated with exactly that guard, and the counterexample that motivates
it (the even-weight code `n = 3, q = 2, d = 2` at `|S| = 2 = k > d - 1`) is
recorded in `ComputationalEvidence.md`.

Experiment (Experimenter, failed run): the natural next step — "both marginals of a
pure state have equal entropy, hence `I(A:B) = 2 |S| log q`" — could *not* be
carried out with `Matrix.charpoly_mul_comm`, which is stated for square matrices
only, whereas the code-state coefficient matrix is genuinely rectangular
(`q ^ |S|` by `q ^ (n - |S|)`).  Rather than assume the rectangular statement, the
mutual-information result is recorded as the two-sided sandwich that the available
machinery actually proves; closing the gap is Direction 3 of
`FUTURE_DIRECTIONS.md`.

Critique (Critic): `entanglementEntropy_codeState_of_isMDS` is not vacuous — the
regime `|S| ≤ min(k, d-1)` is nonempty for every MDS code with `d ≥ 2` and
`k ≥ 1`, and `CutIndexedExamples.lean` exhibits a concrete instance where the
hypotheses are verified by `decide`.
-/

open Finset Matrix
open scoped ComplexOrder

namespace CutIndexedSingleton

open IITTensorNetwork

variable {n q : ℕ}

/-! ## Gluing the two sides of a cut -/

/-- Reassemble a word from its restrictions to a cut and to its complement. -/
def glue (S : Finset (Fin n)) (a : {i // i ∈ S} → Fin q) (b : {i // i ∈ Sᶜ} → Fin q) :
    Word n q :=
  fun i => if h : i ∈ S then a ⟨i, h⟩ else b ⟨i, Finset.mem_compl.mpr h⟩






/-! ## The uniform code state -/

/-- The coefficient matrix, across the cut `S`, of the uniform superposition over
the codebook `C`. -/
noncomputable def codeState (C : Finset (Word n q)) (S : Finset (Fin n)) :
    Matrix ({i // i ∈ S} → Fin q) ({i // i ∈ Sᶜ} → Fin q) ℂ :=
  Matrix.of fun a b => if glue S a b ∈ C then (((Real.sqrt C.card)⁻¹ : ℝ) : ℂ) else 0




/-! ## Bond dimension of the code state -/





/-! ## Exact saturation for MDS codes -/







end CutIndexedSingleton


