-- Prove2me | solution 1 for CutIndexedSingleton.cutEntropy_of_isMDS
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:46:04.020002+00:00
-- url     : https://prove2.me/submissions/d3b41cfc-2431-42e4-99dd-fdd0f94b7f5e

-- Sol generated from Novelty/CutIndexedEntropy.lean
import Mathlib
import Definitions.Def_Novelty_CutIndexedEntropy
import Definitions.Def_Novelty_CutIndexedSingleton
import Definitions.Def_Novelty_IITTensorNetworkEntropy
import Theorems.Thm_CutIndexedSingleton_cutEntropy_eq_log_of_uniform
import Theorems.Thm_CutIndexedSingleton_cutRank_eq_card_of_minDist
import Theorems.Thm_CutIndexedSingleton_cutRank_eq_pow_of_isMDS
import Theorems.Thm_CutIndexedSingleton_fiber_card_of_isMDS
import Theorems.Thm_CutIndexedSingleton_hammingDist_le_of_proj_eq

/-!
# Cut-indexed defects II: the entropy profile of a cut

`CutIndexedSingleton.lean` proved the cut-wise Singleton inequality
`|C| ≤ q ^ (k - |S|) * cutRank C S` for the *counting* bond dimension of a code.
This file replaces counting by **Shannon entropy** and asks when the resulting
entropic inequality is an equality.

## The cut entropy

Put the uniform distribution on the codebook `C` and push it forward to the cut
`S`: the pattern `y : S → Fin q` receives probability
`cutProb C S y = |fibre over y| / |C|`.  Its Shannon entropy `cutEntropy C S` is
the entropy of the marginal seen by the sites in `S` — the classical shadow of
the entanglement entropy across the cut.

## Main results

* `sum_cutProb`, `support_cutProb` : `cutProb` is a probability vector whose
  support is exactly the set of realised patterns, of size `cutRank C S`;
* `cutEntropy_le_log_cutRank` : the entropy of a cut is at most the log of its
  bond dimension (reusing `IITTensorNetwork.sum_negMulLog_le_log_card_support`);
* `cutEntropy_le_min` : **entropic cut-wise Singleton.**  For a code of minimum
  distance `d`, `H(S) ≤ min (|S|, k) * log q` — the entropy profile is trapped
  under the "Ryu–Takayanagi"-shaped plateau curve;
* `entropyDefect_nonneg` : the *entropic cut defect* `|S| log q - H(S)` is
  nonnegative;
* `cutEntropy_of_isMDS` : **the plateau is attained.**  For an MDS code,
  `H(S) = min (|S|, k) * log q` at *every* cut: the profile rises with unit slope
  `log q` up to `|S| = k` and is exactly flat afterwards;
* `isMDS_iff_cutEntropy_eq` : **equality with entropy is equivalent to MDS.**
  Given minimum distance `d` and any single cut `S` of size `k`, the code is MDS
  if and only if the entropy of that one cut equals `k log q`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the combinatorial defect `q ^ (k-|S|) rank S - |C|`
should have an entropic avatar whose vanishing is *equivalent* to the MDS
property, and the entropy profile of an MDS code should be the piecewise-linear
`min(|S|, k) log q` — a discrete Ryu–Takayanagi curve with a sharp corner at the
Singleton dimension.

Experiment (Experimenter): both halves were proved.  The upward slope comes from
`fiber_card_of_isMDS` (balanced fibres force a *uniform* marginal on `q ^ |S|`
patterns); the plateau comes from `cutRank_eq_card_of_minDist` (above `k` the
projection is injective, so the marginal is uniform on all of `C`).  Both cases
are instances of one lemma, `cutEntropy_eq_log_of_uniform`.

Analysis (Analyst): the "needs a different definition" verdict of cycle 1 applies
to the converse direction: `H(S) = |S| log q` for a *single* cut of size `k` is
already enough for MDS, because Shannon entropy of the marginal never exceeds
`log |C|`.  So the whole Singleton defect is detectable at one cut — no averaging
over cuts is needed.  This is what makes `isMDS_iff_cutEntropy_eq` an `iff`.

Critique (Critic): the equivalence needs `2 ≤ q` (for `q = 1` all logs vanish and
the criterion is vacuous) and `C.Nonempty` (the empty code has no marginal); both
hypotheses are recorded explicitly and are necessary.
-/

open Finset

open CutIndexedSingleton

variable {n q : ℕ}













/-! ### Flat marginals -/





open CutIndexedSingleton in
theorem solution{C : Finset (Word n q)} {d : ℕ} (hmds : IsMDS C d)
    (hd1 : 1 ≤ d) (hdn : d ≤ n + 1) (hq : 0 < q) (S : Finset (Fin n)) :
    cutEntropy C S = (min S.card (CutData.sdim n d) : ℕ) * Real.log q := by
  classical
  set k := CutData.sdim n d with hk
  have hCcard : C.card = q ^ k := hmds.2
  have hCne : C.Nonempty := by
    rw [← Finset.card_pos, hCcard]
    exact Nat.pow_pos hq
  rcases le_total S.card k with h | h
  · -- below the plateau: uniform on `q ^ |S|` patterns
    rw [Nat.min_eq_left h]
    have hrank : cutRank C S = q ^ S.card := cutRank_eq_pow_of_isMDS hmds hd1 hq h
    have huni : ∀ y ∈ C.image (proj S), cutProb C S y = (((q ^ S.card : ℕ) : ℝ))⁻¹ := by
      intro y _
      have hfib : (fiber C S y).card = q ^ (k - S.card) := fiber_card_of_isMDS hmds hd1 h y
      unfold cutProb
      rw [hfib, hCcard]
      have hsplit : (q : ℝ) ^ k = (q : ℝ) ^ (k - S.card) * (q : ℝ) ^ S.card := by
        rw [← pow_add]
        congr 1
        omega
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq
      push_cast
      rw [hsplit]
      rw [div_eq_iff (by positivity)]
      field_simp
    rw [cutEntropy_eq_log_of_uniform (Nat.pow_pos hq) hrank huni]
    push_cast
    rw [Real.log_pow]
  · -- above the plateau: uniform on all of `C`
    rw [Nat.min_eq_right h]
    have hres : cutRank C S = C.card := by
      refine cutRank_eq_card_of_minDist hmds.1 ?_
      have : k ≤ S.card := h
      simp only [hk, CutData.sdim] at this ⊢
      omega
    have huni : ∀ y ∈ C.image (proj S), cutProb C S y = ((C.card : ℝ))⁻¹ := by
      intro y hy
      have hfib : (fiber C S y).card = 1 := by
        have hinj : Set.InjOn (proj S) (C : Set (Word n q)) := by
          intro x hx z hz hxz
          by_contra hne
          have h1 := hmds.1 x hx z hz hne
          have h2 := hammingDist_le_of_proj_eq hxz
          have : k ≤ S.card := h
          simp only [hk, CutData.sdim] at this
          omega
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hy
        rw [Finset.card_eq_one]
        refine ⟨c, ?_⟩
        ext z
        simp only [fiber, Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hz, hpz⟩
          exact hinj hz hc hpz
        · rintro rfl
          exact ⟨hc, rfl⟩
      unfold cutProb
      rw [hfib]
      simp
    have hCpos : 0 < C.card := Finset.card_pos.mpr hCne
    rw [cutEntropy_eq_log_of_uniform hCpos hres huni, hCcard]
    push_cast
    rw [Real.log_pow]
