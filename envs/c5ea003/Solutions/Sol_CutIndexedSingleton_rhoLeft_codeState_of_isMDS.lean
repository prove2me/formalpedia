-- Prove2me | solution 1 for CutIndexedSingleton.rhoLeft_codeState_of_isMDS
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:01:26.242482+00:00
-- url     : https://prove2.me/submissions/2662537a-0a63-44d7-8c36-f5c3316dd8a9

-- Sol generated from Novelty/CutIndexedTensorNetwork.lean
import Mathlib
import Definitions.Def_Novelty_CutIndexedEntropy
import Definitions.Def_Novelty_CutIndexedSingleton
import Definitions.Def_Novelty_CutIndexedTensorNetwork
import Definitions.Def_Novelty_IITTensorNetworkMPS
import Definitions.Def_Novelty_IITTensorNetworkSchmidt
import Theorems.Thm_CutIndexedSingleton_card_completions
import Theorems.Thm_CutIndexedSingleton_fiber_card_of_isMDS
import Theorems.Thm_CutIndexedSingleton_hammingDist_le_of_proj_eq

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


@[simp] lemma proj_glue_self (S : Finset (Fin n)) (a : {i // i ∈ S} → Fin q)
    (b : {i // i ∈ Sᶜ} → Fin q) : proj S (glue S a b) = a := by
  funext i
  simp [proj, glue, i.2]

@[simp] lemma proj_compl_glue (S : Finset (Fin n)) (a : {i // i ∈ S} → Fin q)
    (b : {i // i ∈ Sᶜ} → Fin q) : proj Sᶜ (glue S a b) = b := by
  funext i
  have hi : (i : Fin n) ∉ S := Finset.mem_compl.mp i.2
  simp [proj, glue, hi]


lemma glue_injective (S : Finset (Fin n)) {a a' : {i // i ∈ S} → Fin q}
    {b b' : {i // i ∈ Sᶜ} → Fin q} (h : glue S a b = glue S a' b') : a = a' ∧ b = b' := by
  constructor
  · rw [← proj_glue_self S a b, ← proj_glue_self S a' b', h]
  · rw [← proj_compl_glue S a b, ← proj_compl_glue S a' b', h]


/-! ## The uniform code state -/


lemma amp_sq {C : Finset (Word n q)} (hC : C.Nonempty) :
    ((Real.sqrt C.card)⁻¹ : ℝ) ^ 2 = ((C.card : ℝ))⁻¹ := by
  have hpos : (0 : ℝ) < C.card := by exact_mod_cast Finset.card_pos.mpr hC
  rw [inv_pow, Real.sq_sqrt hpos.le]



/-! ## Bond dimension of the code state -/





/-! ## Exact saturation for MDS codes -/








open CutIndexedSingleton in
theorem solution{C : Finset (Word n q)} {d : ℕ} (hmds : IsMDS C d)
    (hd1 : 1 ≤ d) (hq : 0 < q) {S : Finset (Fin n)} (hSk : S.card ≤ CutData.sdim n d)
    (hSd : S.card < d) :
    rhoLeft (codeState C S) = ((((q ^ S.card : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) • (1 : Matrix _ _ ℂ) := by
  classical
  have hCcard : C.card = q ^ CutData.sdim n d := hmds.2
  have hCne : C.Nonempty := by
    rw [← Finset.card_pos, hCcard]
    exact Nat.pow_pos hq
  have hNpos : (0 : ℝ) < C.card := by exact_mod_cast Finset.card_pos.mpr hCne
  ext a a'
  rw [rhoLeft, Matrix.mul_apply]
  by_cases haa : a = a'
  · subst haa
    -- diagonal: count the completions of `a`, i.e. the fibre of the projection
    have hterm : ∀ b : {i // i ∈ Sᶜ} → Fin q,
        codeState C S a b * (codeState C S)ᴴ b a
          = if glue S a b ∈ C then ((((C.card : ℝ))⁻¹ : ℝ) : ℂ) else 0 := by
      intro b
      by_cases h : glue S a b ∈ C
      · simp only [codeState, Matrix.of_apply, Matrix.conjTranspose_apply, if_pos h,
          RCLike.star_def, Complex.conj_ofReal]
        rw [← Complex.ofReal_mul, ← sq, amp_sq hCne]
      · simp [codeState, Matrix.conjTranspose_apply, h]
    rw [Finset.sum_congr rfl fun b _ => hterm b, ← Finset.sum_filter, Finset.sum_const,
      card_completions S a, nsmul_eq_mul]
    rw [fiber_card_of_isMDS hmds hd1 hSk a, hCcard]
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have hreal : ((q ^ (CutData.sdim n d - S.card) : ℕ) : ℝ)
        * (((q ^ CutData.sdim n d : ℕ) : ℝ))⁻¹ = (((q ^ S.card : ℕ) : ℝ))⁻¹ := by
      push_cast
      field_simp
      rw [← pow_add]
      congr 1
      omega
    have hcast := congrArg (fun x : ℝ => (x : ℂ)) hreal
    push_cast at hcast ⊢
    exact hcast
  · -- off diagonal: two codewords agreeing off `S` are within distance `|S| < d`
    have hterm : ∀ b : {i // i ∈ Sᶜ} → Fin q,
        codeState C S a b * (codeState C S)ᴴ b a' = 0 := by
      intro b
      by_cases h1 : glue S a b ∈ C
      · by_cases h2 : glue S a' b ∈ C
        · exfalso
          have hne : glue S a b ≠ glue S a' b := by
            intro hcon
            exact haa (glue_injective S hcon).1
          have hdist := hmds.1 _ h1 _ h2 hne
          have hproj : proj Sᶜ (glue S a b) = proj Sᶜ (glue S a' b) := by simp
          have hle := hammingDist_le_of_proj_eq hproj
          have hcompl : (Sᶜ).card = n - S.card := by
            rw [Finset.card_compl, Fintype.card_fin]
          rw [hcompl] at hle
          have hSn : S.card ≤ n := Finset.card_le_univ S |>.trans (by simp)
          omega
        · simp [codeState, Matrix.conjTranspose_apply, h2]
      · simp [codeState, Matrix.conjTranspose_apply, h1]
    rw [Finset.sum_congr rfl fun b _ => hterm b, Finset.sum_const_zero]
    simp [Matrix.smul_apply, Matrix.one_apply_ne haa]
