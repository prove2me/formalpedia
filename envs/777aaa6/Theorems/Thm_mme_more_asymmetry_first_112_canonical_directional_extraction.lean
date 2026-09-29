-- Prove2me | Theorems.Thm_mme_more_asymmetry_first_112_canonical_directional_extraction
-- name    : mme_more_asymmetry_first_112_canonical_directional_extraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-06T22:44:04.120759+00:00
-- url     : https://prove2.me/theorems/24b626a1-09d5-4f55-9d6d-0c8d0545b83a
-- title:
--   Cofinal canonical112 extraction at the exact released profile with joint directional counts
-- statement:
--   Choose once the exact three complete profiles $\beta$ of the released first active $112$ consumer. Put $D=1180591620717411303424$, $l=8959763742786037$ and $g=1180582660953668517387$. There exists one $C\ge0$ such that, for every sufficiently large $m$, the compatible parameters $N=Dm$, $L=lm$, $G=gm$ admit an induced family with $A>0$ outer stars and $H>0$ components per star. With $Z=\binom{2N}{L}\binom{2N-L}{L}$, its counts satisfy
--
--   $$H\le4^N,\qquad Z e^{-C\sqrt{N+1}}\le A,\qquad \binom{2N}{N}e^{-2C\sqrt{N+1}}\le4AH.$$
--
--   For the same counts, over every field and at every nonnegative tolerance, the actual canonical $112$ block of $\mathrm{CW}_5^{\otimes2}$, raised to power $2N$ and simultaneously filtered in all three complete profiles, contains a genuine $A$-star, $H$-component C-tensor family with component volume $5^{4G+2L}$.
--
--   The profiles, loss constant and finite combinatorial family are selected before the field and tolerance. In particular, family existence is a conclusion, not an assumed extraction. The separate capacities $A$ and $AH$ are retained; no minimum is taken separately for this consumer. This finite cofinal result does not certify entropy limits, a scalar value, the other released consumers, the global recursive extraction or a lower matrix-multiplication exponent.
-- source:
--   Finite assembly for Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/abs/2404.16349v2, Definitions3.4–3.6 (printed pp14–15), at the pinned first active112 profile: OSF https://osf.io/mw5ak/, data/W1.00_2.371339.mat params(923), SHA256783353fda82acb3fb93c247dcad857b2db5f61944f5d0e91ae5f9e5a6c7feec3. Uniform-star square-root losses reuse the earlier q-independent CW/DWZ finite theorem ff1bc517-79c4-4b19-80e0-7c8195bc94c4. The joint binomial identity is exact finite combinatorics, not a use of the paper's final optimized inequality. Source directional aggregation is TermInfoLv2.m lines134–146 and Workspace.m lines211–222 (sums before minima).

import Definitions.Def_mme_more_asymmetry_first_112_profile_data
import Definitions.Def_mme_complete_split_112_canonical_source_data
import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_CW_q6_primary_hash_family
import Mathlib.Analysis.SpecialFunctions.Exp

open MME MME.CompleteSplit MME.CompleteSplit112 Filter
open scoped NNReal

universe u

set_option autoImplicit false

theorem mme_more_asymmetry_first_112_canonical_directional_extraction :
    ∃ beta : Fin 3 → Profile 2,
      (∀ mode sigma, (beta mode).probability sigma =
        (MoreAsymmetryFirstSlice.probability 0 mode sigma : ℝ)) ∧
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ᶠ m : ℕ in atTop,
          let N : ℕ := 1180591620717411303424 * m
          let L : ℕ := 8959763742786037 * m
          let G : ℕ := 1180582660953668517387 * m
          let Zcount : ℕ := Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
          ∃ A H : ℕ, ∃ _family : CWQ6PrimaryHashFamily N L G A H,
            0 < A ∧ H ≤ 4 ^ N ∧
            (Zcount : ℝ) * Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ (A : ℝ) ∧
            (Nat.choose (2 * N) N : ℝ) *
              Real.exp (-2 * C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤
              4 * (A : ℝ) * (H : ℝ) ∧
            ∀ (K : Type u) [Field K] (epsilon : ℝ≥0),
              Nonempty
                (CTensorOneHOneFamilyCertificate
                  (restrictedCanonicalPower K 5 beta epsilon (2 * N))
                  A H (5 ^ (4 * G + 2 * L))) := by sorry
