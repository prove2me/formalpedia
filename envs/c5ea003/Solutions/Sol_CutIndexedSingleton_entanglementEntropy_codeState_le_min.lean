-- Prove2me | solution 1 for CutIndexedSingleton.entanglementEntropy_codeState_le_min
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:01:20.644709+00:00
-- url     : https://prove2.me/submissions/2bef63a9-4df0-4c0a-8604-b54396061c3f

-- Sol generated from Novelty/CutIndexedTensorNetwork.lean
import Mathlib
import Definitions.Def_Novelty_CutIndexedEntropy
import Definitions.Def_Novelty_CutIndexedSingleton
import Definitions.Def_Novelty_CutIndexedTensorNetwork
import Definitions.Def_Novelty_IITTensorNetworkMPS
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Theorems.Thm_CutIndexedSingleton_CutData_rank_le_pow
import Theorems.Thm_CutIndexedSingleton_hasBondDim_codeState
import Theorems.Thm_CutIndexedSingleton_normalized_codeState
import Theorems.Thm_CutIndexedSingleton_singleton_bound_of_minDist
import Theorems.Thm_IITTensorNetwork_entanglementEntropy_le_log_schmidtRank
import Theorems.Thm_IITTensorNetwork_schmidtRank_le_of_hasBondDim
import Theorems.Thm_IITTensorNetwork_schmidtRank_pos

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

open CutIndexedSingleton

open IITTensorNetwork

variable {n q : ℕ}

/-! ## Gluing the two sides of a cut -/







/-! ## The uniform code state -/





/-! ## Bond dimension of the code state -/


/-- **Schmidt rank of the code state is at most the classical bond dimension.** -/
theorem schmidtRank_codeState_le (C : Finset (Word n q)) (S : Finset (Fin n)) :
    schmidtRank (codeState C S) ≤ cutRank C S :=
  schmidtRank_le_of_hasBondDim (hasBondDim_codeState C S)



/-! ## Exact saturation for MDS codes -/








open CutIndexedSingleton in
theorem solution{C : Finset (Word n q)} {d : ℕ}
    (hC : C.Nonempty) (hd : MinDist C d) (hd1 : 1 ≤ d) (S : Finset (Fin n)) :
    entanglementEntropy (codeState C S) ≤ (min S.card (CutData.sdim n d) : ℕ) * Real.log q := by
  classical
  have hnorm := normalized_codeState hC S
  have h1 := entanglementEntropy_le_log_schmidtRank hnorm
  have hrk : 1 ≤ schmidtRank (codeState C S) := schmidtRank_pos hnorm
  have h2 : (schmidtRank (codeState C S) : ℝ) ≤ (cutRank C S : ℝ) := by
    exact_mod_cast schmidtRank_codeState_le C S
  have hpos : (0 : ℝ) < schmidtRank (codeState C S) := by exact_mod_cast hrk
  have h3 : Real.log (schmidtRank (codeState C S)) ≤ Real.log (cutRank C S) :=
    Real.log_le_log hpos h2
  have hcut : Real.log (cutRank C S) ≤ (min S.card (CutData.sdim n d) : ℕ) * Real.log q := by
    have hrankpos : (0 : ℝ) < cutRank C S := by
      have : 0 < cutRank C S := by
        rw [cutRank, Finset.card_pos]
        exact hC.image _
      exact_mod_cast this
    rcases le_total S.card (CutData.sdim n d) with h | h
    · rw [Nat.min_eq_left h]
      have hb : (cutRank C S : ℝ) ≤ ((q : ℝ)) ^ S.card := by
        exact_mod_cast (codeCutData C).rank_le_pow S
      have := Real.log_le_log hrankpos hb
      rwa [Real.log_pow] at this
    · rw [Nat.min_eq_right h]
      have hb : (cutRank C S : ℝ) ≤ ((q : ℝ)) ^ (CutData.sdim n d) := by
        have h4 : cutRank C S ≤ C.card := Finset.card_image_le
        have h5 : C.card ≤ q ^ CutData.sdim n d := singleton_bound_of_minDist hd hd1
        exact_mod_cast h4.trans h5
      have := Real.log_le_log hrankpos hb
      rwa [Real.log_pow] at this
  linarith
