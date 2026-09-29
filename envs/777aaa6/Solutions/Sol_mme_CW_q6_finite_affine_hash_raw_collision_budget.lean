-- Prove2me | solution 1 for mme_CW_q6_finite_affine_hash_raw_collision_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T20:55:43.692014+00:00
-- url     : https://prove2.me/submissions/eec2d182-f3d6-4618-9521-fc615b8fc4f4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_CW_q6_primary_hash_bucket_collision_budget_averaging
import Theorems.Thm_mme_CW_q6_primary_hash_bucket_structure

open MME

noncomputable local instance q6RawSplitExactAddressDecidableEq
    (N L G : ℕ) : DecidableEq (CWQ6ExactCoupledAddress N L G) :=
  Classical.decEq _

/-- Instantiate the literal bucket at the favorable averaged affine
parameters, then attach its proved structural bounds and closure. -/
theorem solution :
    ∃ d : ℕ, 0 < d ∧
      ∀ (N L G : ℕ),
        CWQ6ExactAddressRegularity N L G →
        (0 < L ∧ L + G = N ∧ 341 * L < 100 * G) →
        let Zcount : ℕ :=
          Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
        let Xcount : ℕ := Nat.choose N G
        let middle : ℕ := Nat.choose (2 * G) G
        let Mmod : ℕ := 4 * Xcount ^ 2 + 1
        ∀ S : Finset ℕ,
          S ⊆ Finset.range (Mmod / 2) →
          ThreeAPFree (S : Set ℕ) →
          0 < S.card →
          ∃ E : Finset (CWQ6ExactCoupledAddress N L G),
            ∃ H : ℕ,
              0 < H ∧
              (E.image (fun e => e.1 2)).card ≤ Zcount ∧
              (∀ c ∈ E.image (fun e => e.1 2),
                (E.filter (fun e => e.1 2 = c)).card ≤ middle) ∧
              (∀ ex ∈ E, ∀ ey ∈ E, ∀ ez ∈ E,
                CWQ6CoupledCoordinatewiseSupported
                    (cwQ6CoupledMixedAddress ex.1 ey.1 ez.1) →
                  ∃ e' ∈ E,
                    e'.1 0 = ex.1 0 ∧
                    e'.1 1 = ey.1 1 ∧
                    e'.1 2 = ez.1 2) ∧
              H ≤ 4 ^ N ∧
              (middle : ℝ) *
                  ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                    (((N + 1 : ℕ) : ℝ) ^ d)) ≤
                4 * (Xcount : ℝ) ^ 2 * (H : ℝ) ∧
              (H : ℝ) * (Zcount : ℝ) +
                    (middle : ℝ) *
                      ((Zcount : ℝ) *
                        ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                          (((N + 1 : ℕ) : ℝ) ^ d))) +
                    (((E.product E).filter (fun p =>
                      p.1 ≠ p.2 ∧
                        (p.1.1 0 = p.2.1 0 ∨
                          p.1.1 1 = p.2.1 1))).card : ℝ) ≤
                (E.card : ℝ) := by
  obtain ⟨d, hd, havg⟩ :=
    mme_CW_q6_primary_hash_bucket_collision_budget_averaging
  refine ⟨d, hd, ?_⟩
  intro N L G hregular hprofile
  dsimp only
  intro S hSrange hSfree hSpos
  obtain ⟨b0, w, H, hH, hHupper, hmiddle, hmass⟩ :=
    havg N L G hregular hprofile S hSrange hSfree hSpos
  let E := cwQ6PrimaryHashBucket N L G (Nat.choose N G) S b0 w
  have hstruct := mme_CW_q6_primary_hash_bucket_structure
    N L G (Nat.choose N G) hregular S hSrange hSfree b0 w
  dsimp only at hstruct
  exact ⟨E, H, hH, hstruct.1, hstruct.2.1, hstruct.2.2,
    hHupper, hmiddle, hmass⟩
