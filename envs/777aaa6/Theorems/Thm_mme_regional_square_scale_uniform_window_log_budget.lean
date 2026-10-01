-- Prove2me | Theorems.Thm_mme_regional_square_scale_uniform_window_log_budget
-- name    : mme_regional_square_scale_uniform_window_log_budget
-- status  : Proved
-- author  : @BrunoDCDO
-- created : 2026-09-24T02:24:33.235624+00:00
-- url     : https://prove2.me/theorems/2273afa5-2570-43da-8e72-84e0630074d4
-- title:
--   Uniform finite-loss regional budgets for all nearby profiles at square scales
-- statement:
--   Fix finite integer regional data $(n,m,\mu)$, with at least one parent type, positive count for every parent type, and exact split and cell mass identities. Let $E_0$ be their regional entropy rate. For every $a>0$ and every real $r<E_0$, there exists $\delta>0$ such that, for all sufficiently large natural numbers $k$, the following holds uniformly over every exact profile $\nu$ with the scaled cell masses and every reference address for the counts $k^2n$.
--
--   If every cell frequency of $\nu$ differs by at most $\delta$ from the corresponding frequency of $k^2\mu$, set
--
--   $$
--   \varepsilon_k=\sqrt{a(k+2)/k^2},\qquad h_k=\operatorname{Nat.log}_k(\mathrm{capacity}(\nu))+1.
--   $$
--
--   The full finite-loss logarithmic budget at repair base $k$ is at least $rk^2$:
--
--   $$
--   \begin{aligned}
--   rk^2\le{}&E(\nu)-k^2\Bigl(\sum_j n_j\Bigr)\,\operatorname{entropyModulus}(\varepsilon_k)\\
--   &-4\sqrt{\log F_k+\Theta(\nu,\varepsilon_k)}-\log(64P_kF_k)-h_k\log 8.
--   \end{aligned}
--   $$
--
--   Here $F_k$, $P_k$, $\Theta$, and capacity are the canonical scale factor, polynomial factor, scale exponent, and product of the three exact block cardinalities. They are expanded in the formal statement. The bound includes profiles with zero-mass cells and capacity zero. The threshold is independent of the profile and reference address. Support and boundary compatibility are not needed for this scalar inequality; applications to extraction stages retain their separate admissibility and source hypotheses.
-- source:
--   Adaptation of marwahaha's [graded regional band-rate proof](p2m:solution/7a5b2129-a01d-4d23-9c67-a0210067a914), for [the accepted band-rate theorem](p2m:theorem/c2fa0f18-5520-433f-bc2c-2b454f76f5c7). It combines the [regional homogeneity theorem](p2m:theorem/8f9bbf87-fe2f-4441-93c8-ad9183ab02b1), Gandalf's [explicit entropy-modulus bound](p2m:theorem/32b80025-891b-42f8-8ed3-b75f92f71601), and raresbuhai's [word-capacity](p2m:theorem/97d1fbac-88d2-46f1-90fd-a82674c29b5f) and [square-scale repair](p2m:theorem/6afb1c6c-58ad-4c5a-aebe-148b9224a767) estimates. The tolerance-window interpretation follows Section 6 of Alman et al., More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6. This scalar interface is a formal adaptation, not a verbatim theorem from the paper.

import Definitions.Def_mme_regional_tolerance_window_data

open BigOperators Filter MME MME.RegionRate MME.RegionRealization
  MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
set_option autoImplicit false

theorem mme_regional_square_scale_uniform_window_log_budget
    {ell half R : ℕ} (parent : Fin R → Fin 3 → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (hn : ∀ r, 0 < n r) (hR : 0 < R)
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (hm : ∀ r, ∑ c, m r c = n r)
    (mu : Fin 3 → Cell half R parent → CompleteWord ell → ℕ)
    (hmass : ∀ i cell, ∑ w, mu i cell w =
      m cell.1 cell.2 + m cell.1 (complement (htotal cell.1) cell.2))
    (a : ℝ) (ha : 0 < a) (rate : ℝ)
    (hrate : rate < regionalRate htotal n m mu) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ᶠ k : ℕ in atTop,
      ∀ profile : Fin 3 → Cell half R parent → CompleteWord ell → ℕ,
        (∀ i cell, ∑ w, profile i cell w =
          k ^ 2 * m cell.1 cell.2 +
            k ^ 2 * m cell.1 (complement (htotal cell.1) cell.2)) →
        (∀ i cell w, |cellFrequency (profile i) cell w -
          cellFrequency (fun cell w => k ^ 2 * mu i cell w) cell w| ≤ delta) →
      ∀ reference : Address half R parent (fun r => k ^ 2 * n r),
        let epsilon := Real.sqrt (a * ((k + 2 : ℕ) : ℝ) / (k : ℝ) ^ 2)
        let capacity := ∏ i : Fin 3, Nat.card (Block ell (fullCell htotal reference)
          (fun cell i => (cell.2.val i).val) profile i)
        let repairExponent := Nat.log k capacity + 1
        let energy := regionalRate htotal (fun r => k ^ 2 * n r)
          (fun r cell => k ^ 2 * m r cell) profile
        let loss := ((∑ r, k ^ 2 * n r : ℕ) : ℝ) *
          entropyModulus (Fin 2 → CompleteWord ell) epsilon
        let theta := scaleExponent htotal (fun r => k ^ 2 * n r)
          (fun r cell => k ^ 2 * m r cell) profile epsilon
        let factor := scaleFactor (half := half) (parent := parent)
          (fun r => k ^ 2 * n r) k ell
        rate * (k : ℝ) ^ 2 ≤ energy - loss -
          4 * Real.sqrt (Real.log factor + theta) -
          Real.log (64 * polynomialFactor (fun r => k ^ 2 * n r)
            (Fintype.card (Cell half R parent)) * factor) -
          repairExponent * Real.log 8 := by sorry
