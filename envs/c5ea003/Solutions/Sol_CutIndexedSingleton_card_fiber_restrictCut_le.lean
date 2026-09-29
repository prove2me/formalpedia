-- Prove2me | solution 1 for CutIndexedSingleton.card_fiber_restrictCut_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:20:40.52931+00:00
-- url     : https://prove2.me/submissions/0da4b59d-85cf-47fd-be1e-18e519521dce

-- Sol generated from Novelty/CutIndexedEntropicSingleton.lean
import Mathlib
import Definitions.Def_Novelty_CutIndexedEntropicSingleton
import Definitions.Def_Novelty_CutIndexedEntropyMono

/-!
# Cut-indexed defects VI: the entropic cut-wise Singleton inequality

File I proved the *counting* cut-wise Singleton inequality
`|C| ≤ q ^ (k - |S|) * cutRank C S`.  File V showed that the entropy profile
`S ↦ cutEntropy C S` is monotone.  This file completes the entropic mirror of the
`CutData` axioms by proving the missing **chain-rule bound**
`H(T) ≤ H(S) + (|T| - |S|) log q`, and deduces the sharpest form of the theory:

`log |C| ≤ H(S) + (k - |S|) log q` for every cut with `|S| ≤ k = n + 1 - d`.

Because `H(S) ≤ log (cutRank C S)` always, this **implies** the counting cut-wise
Singleton inequality and is strictly stronger whenever the marginal on `S` is not
uniform.

## Main results

* `sum_negMulLog_le_group` : the *log-sum / grouping* inequality
  `∑_{i ∈ F} negMulLog pᵢ ≤ negMulLog (∑ pᵢ) + (∑ pᵢ) log N` for `|F| ≤ N`;
* `card_fiber_restrictCut_le` : a pattern on `S` has at most `q ^ (|T| - |S|)`
  extensions to `T`;
* `cutEntropy_le_add_of_subset` : **the entropic one-block growth bound**
  `H(T) ≤ H(S) + (|T| - |S|) log q`;
* `cutEntropy_eq_log_card_of_resolving` : above the Singleton dimension the cut
  entropy is exactly `log |C|`;
* `entropic_cutwise_singleton` : **the entropic cut-wise Singleton inequality**;
* `entropic_cutwise_singleton_implies_counting` : it implies the counting version
  of file I;
* `entropicDefect_nonneg`, `entropicDefect_eq_zero_iff_isMDS` : the entropic cut
  defect is nonnegative, and at the empty cut it vanishes exactly for MDS codes.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer, cycle 2): every axiom of `CutData` should have an
entropic mirror, and the mirrored Singleton argument should be *strictly sharper*
than the counting one, because entropy sees the shape of the fibre distribution
and rank only sees its support.

Experiment (Experimenter): the mirror is complete.  The one-block growth bound is
the grouping inequality applied fibre-by-fibre, with `N = q ^ (|T| - |S|)` the
number of extensions of a pattern; the proof of the grouping inequality is the
same `log x ≤ x - 1` estimate that powers
`IITTensorNetwork.sum_negMulLog_le_log_card_support`, but *relativised* to a
sub-block, which is what makes it usable inside a sum over cuts.

Analysis (Analyst): the entropic inequality is strictly stronger: for the code
`{000, 100, 010, 110, 001}` of `Examples.pentaCode` the counting bound at
`S = {0}` is not tight while the entropic one records the exact non-uniformity of
the fibres.  The mirror also explains file III: the quantum inequality is a third
member of the same family, with `log (Schmidt rank)` in place of `H(S)`, and it is
the only one of the three that can *fail* to saturate for MDS codes, because of
purity on the complement.

Critique (Critic): the equality analysis at the empty cut needs `2 ≤ q` (for
`q = 1` all logarithms vanish and the criterion is vacuous) and `C.Nonempty`;
`entropicDefect_eq_zero_iff_isMDS` records both.
-/

open Finset

open CutIndexedSingleton

variable {n q : ℕ}

/-! ## The grouping (log-sum) inequality -/


/-! ## Counting the extensions of a pattern -/


/-! ## The entropic chain-rule bound -/


/-! ## The entropic cut-wise Singleton inequality -/








open CutIndexedSingleton in
theorem solution{S T : Finset (Fin n)} (h : S ⊆ T)
    (y : {i // i ∈ S} → Fin q) :
    ((Finset.univ : Finset ({i // i ∈ T} → Fin q)).filter
        (fun z => restrictCut h z = y)).card ≤ q ^ (T.card - S.card) := by
  classical
  have hinj : Set.InjOn
      (fun z : {i // i ∈ T} → Fin q => fun i : {i // i ∈ T \ S} =>
        z ⟨i.1, (Finset.mem_sdiff.mp i.2).1⟩)
      ((Finset.univ.filter (fun z : {i // i ∈ T} → Fin q => restrictCut h z = y) :
        Finset _) : Set _) := by
    intro z hz z' hz' hzz
    have hzy : restrictCut h z = y := by simpa using hz
    have hzy' : restrictCut h z' = y := by simpa using hz'
    funext i
    by_cases hiS : (i : Fin n) ∈ S
    · have h1 : z ⟨i.1, h hiS⟩ = y ⟨i.1, hiS⟩ := congrFun hzy ⟨i.1, hiS⟩
      have h2 : z' ⟨i.1, h hiS⟩ = y ⟨i.1, hiS⟩ := congrFun hzy' ⟨i.1, hiS⟩
      have hi : i = ⟨i.1, h hiS⟩ := Subtype.ext rfl
      rw [hi, h1, h2]
    · have hmem : (i : Fin n) ∈ T \ S := Finset.mem_sdiff.mpr ⟨i.2, hiS⟩
      have := congrFun hzz ⟨i.1, hmem⟩
      simpa using this
  have hle := Finset.card_le_card_of_injOn _
    (fun z _ => Finset.mem_univ
      ((fun i : {i // i ∈ T \ S} => z ⟨i.1, (Finset.mem_sdiff.mp i.2).1⟩))) hinj
  calc ((Finset.univ : Finset ({i // i ∈ T} → Fin q)).filter
        (fun z => restrictCut h z = y)).card
      ≤ (Finset.univ : Finset ({i // i ∈ T \ S} → Fin q)).card := hle
    _ = q ^ (T \ S).card := by
        rw [Finset.card_univ, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin]
    _ = q ^ (T.card - S.card) := by rw [Finset.card_sdiff_of_subset h]
