-- Prove2me | solution 1 for JokeSurpriseStability.paraphrase_bound_sharp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:38:55.505854+00:00
-- url     : https://prove2.me/submissions/be3ff143-c28a-45cc-b9b4-046058361358

-- Sol generated from Applications/JokeSurpriseStability.lean
import Mathlib
import Definitions.Def_Applications_JokeColimitUniversality
import Definitions.Def_Applications_JokeSurpriseAlgebra
import Definitions.Def_Applications_JokeSurpriseStability

/-!
# Stability and correlation for the surprise invariant

`Applications.JokeSurpriseAlgebra` measured the surprise of a setup `S ⊆ ℝ` by its
range `humor S = max' S - min' S`, and `Applications.JokeColimitUniversality` showed
that this invariant is submodular and is maximised at universal (terminal) jokes.

Two questions were left open by that development, and both are prerequisites for the
empirical claim of the programme ("`H(J)` correlates with human funniness ratings"):

1. **Is surprise the shadow of a genuine metric invariant?** If humor is to be a
   *distance* `d(lim S, colim S')` on a category of punchlines, the range model must be
   the one-dimensional case of a metric-space construction.
2. **Is surprise stable?** A rating experiment is meaningless if paraphrasing a joke —
   perturbing each reading by at most `ε` — can change its measured humor arbitrarily.

## Results

### Surprise is a diameter
* `humor_eq_diam` : the catalog's `humor` is *exactly* `Metric.diam` of the setup viewed
  as a subset of `ℝ`. The range model is therefore the `ℝ`-instance of a general
  metric-space invariant `metricHumor s = diam s`.
* `metricHumor_union_le_add_of_shared` : the catalog's subadditivity law generalises
  verbatim to an arbitrary (pseudo)metric space of readings.
* `metricHumor_mono` : monotonicity generalises too.

### Surprise is Lipschitz, hence experimentally meaningful
* `diam_le_diam_add_two_hausdorffDist` and `abs_diam_sub_diam_le_two_hausdorffDist` :
  the metric surprise is **2-Lipschitz for the Hausdorff distance** between setups.
  Two setups that are `δ`-close as configurations of readings have humors differing by
  at most `2δ`.
* `abs_humor_image_sub_humor_le` : the **paraphrase bound**. If every reading is moved
  by at most `ε`, the measured humor moves by at most `2ε`. The constant `2` is sharp
  (`paraphrase_bound_sharp`).

### Correlation with ratings
* `empCov_nonneg_of_monovaryOn` : if funniness ratings *monovary* with humor, the
  empirical covariance of humor and rating is nonnegative. This is the precise,
  provable form of the programme's correlation conjecture (a Chebyshev sum inequality).
* `exists_dataset_empCov_neg` : the hypothesis cannot be dropped — there is a two-joke
  dataset with strictly negative covariance. Correlation is a *property of the data*,
  not a theorem about humor.
* `hundredJokes_empCov_nonneg` : the 100-joke test suite. Jokes `J i` (`i < 100`) with
  setups `{0, i}` have `H(J i) = i`; against any monotone rating model — we use the
  saturating model `R i = min i 50`, reflecting the empirical ceiling of rating scales —
  the covariance of humor and rating is nonnegative.
* `sampleJokes_empCov_pos` : a concrete three-joke sample (pun / wordplay / absurdist)
  with strictly positive covariance.

-- !-- Lab Notes -- !--
Hypothesis (H4): the one-dimensional range model is not ad hoc but is `Metric.diam`.
Hypothesis (H5): surprise is Lipschitz in the Hausdorff metric on setups, with
constant 2, and 2 cannot be improved.
Hypothesis (H6): "humor correlates with funniness" is a theorem.

Experiment: H4 was settled by a two-sided argument (`dist_le_diam_of_mem` at the
extremes, `diam_le_of_forall_dist_le` in general). H5 was proved by an
`ε`-approximation argument through `exists_dist_lt_of_hausdorffDist_lt` plus
`dist_triangle4`, then a `by_contra` limit step; sharpness was witnessed by
`{0,1} ↦ {-1,2}` at `ε = 1`, where the humor gap is exactly `2ε`.
H6 was tested on synthetic datasets of sizes 2, 3 and 100.

Analysis: H4 and H5 survive. H6 is **false as stated**: covariance can be negative
(`exists_dataset_empCov_neg`). What survives is the guarded version: monovariance of
ratings with humor implies nonnegative covariance, via Chebyshev's sum inequality.
The failure is instructive — it is exactly the empirical content of the programme,
and it is *not* derivable from the category theory.

Critique: the Hausdorff bound requires `hausdorffEDist ≠ ⊤` (otherwise the Hausdorff
distance is `0` by convention while the diameters differ arbitrarily) and boundedness
of the comparison set; both hypotheses are load-bearing, not cosmetic. The 100-joke
suite uses a synthetic monotone rating model, so it tests internal consistency of the
formalism rather than human data.

Synthesis: surprise is a diameter, it is 2-Lipschitz for the Hausdorff metric on
setups, and its correlation with funniness is exactly as strong as the monovariance of
the rating data — no stronger.
-/

open Finset Metric JokeSurpriseAlgebra

open JokeSurpriseStability

/-! ### Surprise is a diameter -/





/-! ### Hausdorff stability -/



/-! ### The paraphrase bound -/



/-! ### Correlation with funniness ratings -/




/-! ### The 100-joke test suite -/











open JokeSurpriseStability in
theorem solution:
    ∃ (S : Finset ℝ) (hS : S.Nonempty) (f : ℝ → ℝ) (ε : ℝ),
      (∀ x ∈ S, |f x - x| ≤ ε) ∧
      |humor (S.image f) (hS.image f) - humor S hS| = 2 * ε := by
  classical
  refine ⟨{0, 1}, ⟨0, by simp⟩, fun x => 3 * x - 1, 1, ?_, ?_⟩
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> norm_num
  · have h1 : humor ({0, 1} : Finset ℝ) ⟨0, by simp⟩ = 1 := by
      unfold humor
      have hmax : ({0, 1} : Finset ℝ).max' ⟨0, by simp⟩ = 1 := by
        refine le_antisymm (Finset.max'_le _ _ _ ?_) (Finset.le_max' _ _ (by simp))
        intro y hy; simp at hy; rcases hy with rfl | rfl <;> norm_num
      have hmin : ({0, 1} : Finset ℝ).min' ⟨0, by simp⟩ = 0 := by
        refine le_antisymm (Finset.min'_le _ _ (by simp)) (Finset.le_min' _ _ _ ?_)
        intro y hy; simp at hy; rcases hy with rfl | rfl <;> norm_num
      rw [hmax, hmin]; norm_num
    have h2 : ∀ hne : (({0, 1} : Finset ℝ).image fun x => 3 * x - 1).Nonempty,
        humor (({0, 1} : Finset ℝ).image fun x => 3 * x - 1) hne = 3 := by
      intro hne
      unfold humor
      have hmem2 : (2 : ℝ) ∈ (({0, 1} : Finset ℝ).image fun x => 3 * x - 1) := by
        refine Finset.mem_image.2 ⟨1, by simp, by norm_num⟩
      have hmemm1 : (-1 : ℝ) ∈ (({0, 1} : Finset ℝ).image fun x => 3 * x - 1) := by
        refine Finset.mem_image.2 ⟨0, by simp, by norm_num⟩
      have hmax : (({0, 1} : Finset ℝ).image fun x => 3 * x - 1).max' hne = 2 := by
        refine le_antisymm (Finset.max'_le _ _ _ ?_) (Finset.le_max' _ _ hmem2)
        intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
        simp at hx; rcases hx with rfl | rfl <;> norm_num
      have hmin : (({0, 1} : Finset ℝ).image fun x => 3 * x - 1).min' hne = -1 := by
        refine le_antisymm (Finset.min'_le _ _ hmemm1) (Finset.le_min' _ _ _ ?_)
        intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
        simp at hx; rcases hx with rfl | rfl <;> norm_num
      rw [hmax, hmin]; norm_num
    rw [h1, h2]
    norm_num
