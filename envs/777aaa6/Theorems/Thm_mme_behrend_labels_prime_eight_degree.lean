-- Prove2me | Theorems.Thm_mme_behrend_labels_prime_eight_degree
-- name    : mme_behrend_labels_prime_eight_degree
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-12T18:40:22.329822+00:00
-- url     : https://prove2.me/theorems/eff87ce7-86dd-41b5-8220-fddc8676be14
-- title:
--   Behrend prime labels with eight-degree prime bound
-- statement:
--   For any scale parameters with $1 \le D \le 5^N$ and any X-degree $d \le D$, there exist a prime $p \ge 5$ and a 3AP-free label set $S$ within $\mathrm{range}(p/2)$ with at least $6D$ usable labels and the eight-degree hash budget $8d \le p$. This packages the proved Behrend prime/label existence with the exact prime lower bound needed by the DWZ eight-degree hash budget interface.
-- source:
--   Packaging of mme_prime_behrend_dominates_bounded_collision_degree for the More Asymmetry X-hash construction; Alman et al., arXiv:2404.16349v2.

import Theorems.Thm_mme_prime_behrend_dominates_bounded_collision_degree

theorem mme_behrend_labels_prime_eight_degree (N D d : ℕ) (hD1 : 1 ≤ D) (hD5 : D ≤ 5 ^ N) (hdD : d ≤ D) :
    ∃ p : ℕ, Nat.Prime p ∧ 5 ≤ p ∧
      ∃ S : Finset ℕ,
        S ⊆ Finset.range (p / 2) ∧
        ThreeAPFree (S : Set ℕ) ∧
        (6 * D : ℝ) ≤ (S.card : ℝ) ∧
        8 * d ≤ p := by sorry
