-- Prove2me | solution 1 for Catalog.Geometry.Peel.bodyLayer_volume
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:21:58.696336+00:00
-- url     : https://prove2.me/submissions/4efc2aaa-2527-4287-b606-cc58cb5f211e

-- Sol generated from Geometry/PeelDilationBodies.lean
import Mathlib
import Definitions.Def_Geometry_PeelDilationBodies
import Definitions.Def_Geometry_PeelStoppingTime
import Theorems.Thm_Catalog_Geometry_Peel_equipartitionProfile_gap
/-
# Cycle 3: universality of the matching family

The shell peeling of a Euclidean ball saturates the peeling bound, and the
`O(d)`-action on its layers exhibits the symmetry responsible for that
saturation.  A natural criticism is that this could be an artefact of the
ball: the ball is the most symmetric body there is, so of course it produces a
symmetric peeling.

This file removes that objection: the construction is *universal*.  For **any**
star-shaped body `K ⊆ ℝ^d` of finite measure the dilates
`c_k • K`, `c_k = (1 - k/N)^{1/d}`, peel `K` into `N` pieces of equal measure
`vol K / N` (`bodyPeel_gap`, `bodyLayer_volume`), and every layer is invariant
under the *entire* linear symmetry group of `K` (`bodyLayer_equivariant`).
Conversely, a dilation peeling all of whose layers have measure at most
`vol K / N` must be this one (`body_peel_rigidity`).  The ball family of the
previous file is the special case `K = B(0,1)`, where the symmetry group is
`O(d)`.

The upshot for the original question — a matching family of actions for the
peeling upper bound — is that the extremisers are parameterised by *all* pairs
`(K, G)` with `G` a group of linear symmetries of `K`: the dimension `d` fixes
the radial profile `(1 - k/N)^{1/d}`, and the body `K` is otherwise free.

## Lab notes

Cross-check in `d = 2` with `K` the unit square `[-1,1]^2` (`vol K = 4`) and
`N = 4`: dilation factors `1, √(3)/2, √(2)/2, 1/2, 0`, layer areas
`4·(1/4) = 1` each — identical factors to the disc case, as the theory
predicts: the factors depend only on `d` and `N`, never on `K`.
-/

open Catalog.Geometry.Peel

open Finset MeasureTheory Metric Pointwise

/-! ## Volumes of dilates -/



lemma volume_smul_ne_top {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} (hK : volume K ≠ ⊤)
    {c : ℝ} (hc : 0 ≤ c) : volume (c • K) ≠ ⊤ := by
  rw [MeasureTheory.Measure.addHaar_smul_of_nonneg volume hc K]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hK


/-! ## Star-shaped bodies and nested dilates -/


/-- Dilates of a star-shaped body are nested. -/
lemma smul_subset_smul_of_starShaped {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK : StarShaped K) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : a • K ⊆ b • K := by
  rcases eq_or_lt_of_le (ha.trans hab) with hb | hb
  · have hb0 : b = 0 := hb.symm
    have ha0 : a = 0 := le_antisymm (hb0 ▸ hab) ha
    rw [ha0, hb0]
  · rintro x ⟨y, hy, rfl⟩
    refine ⟨(a / b) • y, hK y hy (a / b) (by positivity) ?_, ?_⟩
    · rw [div_le_one hb]; exact hab
    · show b • ((a / b) • y) = a • y
      rw [smul_smul, mul_div_cancel₀ _ hb.ne']

/-! ## The universal equal-volume dilation peeling -/


lemma dilationFactor_nonneg (d N k : ℕ) : 0 ≤ dilationFactor d N k :=
  Real.rpow_nonneg (le_max_left _ _) _

lemma dilationFactor_anti (d N : ℕ) : Antitone (dilationFactor d N) := by
  intro a b hab
  have hcast : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hmono : max 0 (1 - (b : ℝ) / N) ≤ max 0 (1 - (a : ℝ) / N) := by
    refine max_le_max (le_refl 0) ?_
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    · have hNR : (0 : ℝ) < N := by exact_mod_cast h
      have : (a : ℝ) / N ≤ b / N := by gcongr
      linarith
  exact Real.rpow_le_rpow (le_max_left _ _) hmono (by positivity)

lemma dilationFactor_pow {d N k : ℕ} (hd : 0 < d) :
    (dilationFactor d N k) ^ d = max 0 (1 - (k : ℝ) / (N : ℝ)) :=
  Real.rpow_inv_natCast_pow (le_max_left _ _) hd.ne'




/-- **The geometric identity, universal form.**  The abstract profile of the
dilation peeling is the sequence of measures of the dilates `c_k • K`. -/
theorem bodyPeel_size (d N k : ℕ) (hd : 0 < d) (K : Set (EuclideanSpace ℝ (Fin d))) :
    (bodyPeel d K N).size k = bodyVol d ((dilationFactor d N k) • K) := by
  rw [bodyVol_smul (dilationFactor_nonneg d N k), dilationFactor_pow hd]
  show bodyVol d K * max 0 (1 - (k : ℝ) / (N : ℝ))
      = max 0 (1 - (k : ℝ) / (N : ℝ)) * bodyVol d K
  ring


/-- **Equal measures for an arbitrary body.**  Every one of the `N` dilation
layers of `K` has measure `vol K / N`. -/
theorem bodyPeel_gap (d N k : ℕ) (hN : 0 < N) (hk : k < N)
    (K : Set (EuclideanSpace ℝ (Fin d))) :
    peelGap (bodyPeel d K N) k = bodyVol d K / N :=
  equipartitionProfile_gap (bodyVol_nonneg d K) hN hk




/-! ## Rigidity for arbitrary bodies -/





open Catalog.Geometry.Peel in
theorem solution(d N k : ℕ) (hd : 0 < d) (hN : 0 < N) (hk : k < N)
    {K : Set (EuclideanSpace ℝ (Fin d))} (hmeas : MeasurableSet K) (hfin : volume K ≠ ⊤)
    (hstar : StarShaped K) :
    (volume (bodyLayer d K N k)).toReal = bodyVol d K / N := by
  have hsub : (dilationFactor d N (k + 1)) • K ⊆ (dilationFactor d N k) • K :=
    smul_subset_smul_of_starShaped hstar (dilationFactor_nonneg d N (k + 1))
      (dilationFactor_anti d N (Nat.le_succ k))
  have hnull : NullMeasurableSet ((dilationFactor d N (k + 1)) • K) volume := by
    rcases eq_or_ne (dilationFactor d N (k + 1)) 0 with hc | hc
    · rcases K.eq_empty_or_nonempty with hKe | hne
      · rw [hKe]; simp
      · rw [hc, Set.zero_smul_set hne]
        exact (measurableSet_singleton 0).nullMeasurableSet
    · exact (hmeas.const_smul₀ _).nullMeasurableSet
  have hfin' : volume ((dilationFactor d N (k + 1)) • K) ≠ ⊤ :=
    volume_smul_ne_top hfin (dilationFactor_nonneg d N (k + 1))
  have hdiff : volume (bodyLayer d K N k)
      = volume ((dilationFactor d N k) • K) - volume ((dilationFactor d N (k + 1)) • K) :=
    measure_diff hsub hnull hfin'
  rw [hdiff, ENNReal.toReal_sub_of_le (measure_mono hsub)
    (volume_smul_ne_top hfin (dilationFactor_nonneg d N k))]
  have h1 : bodyVol d ((dilationFactor d N k) • K) = (bodyPeel d K N).size k :=
    (bodyPeel_size d N k hd K).symm
  have h2 : bodyVol d ((dilationFactor d N (k + 1)) • K) = (bodyPeel d K N).size (k + 1) :=
    (bodyPeel_size d N (k + 1) hd K).symm
  show bodyVol d ((dilationFactor d N k) • K)
      - bodyVol d ((dilationFactor d N (k + 1)) • K) = bodyVol d K / N
  rw [h1, h2]
  exact bodyPeel_gap d N k hN hk K
