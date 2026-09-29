-- Prove2me | Theorems.Thm_overlapRealSlide
-- name    : overlapRealSlide
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-26T23:41:38.089906+00:00
-- url     : https://prove2.me/theorems/0c84dacc-1d54-4f9f-a79f-b6002aee268b
-- title:
--   Sliding the real part towards the anchor keeps a point in the matched-cover overlap
-- statement:
--   Let $a = n+1-\tfrac34$, $b = n+1$ and let
--   $$O = \{z : \mathbb{C} \mid a < \operatorname{Re} z,\quad z \in O^{\mathrm{cap}}\},$$
--   where the second condition is $z$ lying in the punctured half-space, i.e.
--   $\operatorname{Re} z < n+1$, or $\operatorname{Im} z > 0$, or $|z-(n+2)|<\tfrac12$.
--   Then for every real $x_0$ with $\langle x_0, 1\rangle \in O$ and every $s\in[0,1]$ the
--   point $\langle (1-s)x_0 + s(a+\tfrac12),\, 1-s\rangle$ again lies in $O$.
--
--   The real part of the image is a convex combination of $x_0$ and the midpoint
--   $a+\tfrac12$ of the interval $(a,b)$, both of which exceed $a$, so the lower bound survives.
--   The imaginary part is $1-s\in[0,1]$, so whenever the real part reaches $b$ the second
--   disjunct applies; and at $s=1$ the image is exactly the anchor
--   $(a+\tfrac12, 0)$, whose real part $a+\tfrac12$ is still below $b$.
--
--   This is the second of the two stages of the explicit contraction of $O$ onto the anchor
--   $(n+\tfrac58, 0)$; the first stage, `overlapImaginarySlide`, is already proved. Together they
--   contract $O$ to a point, after which the subtype transfer
--   (`homeomorphOfSubsetRange` and `Homeomorph.contractibleSpace_iff`) yields
--   `ContractibleSpace` for the overlap in
--   `BraidsLinksMCG.puncturedPlane_standardGen_matched_cover_overlap_contractible_v1`.
-- source:
--   A. Hatcher, Algebraic Topology (2002), Section 1.2 (van Kampen), applied to the explicit two-piece matched cover of the plane punctured at the first n+1 positive integers; the overlap of BraidsLinksMCG.puncturedPlane_standardGen_matched_cover_overlap_contractible_v1, second stage of the explicit contraction.

import Mathlib

theorem overlapRealSlide (n : ℕ) :
    ∀ (x0 : ℝ), (n : ℝ) + 1 - 3 / 4 < x0 →
      (x0 < (n : ℝ) + 1 ∨ 0 < (1 : ℝ) ∨ dist (⟨x0, 1⟩ : ℂ) ((n + 2 : ℕ) : ℂ) < 1 / 2) →
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        (n : ℝ) + 1 - 3 / 4 < (⟨(1 - s) * x0 + s * ((n : ℝ) + 1 - 3 / 4 + 1 / 2), 1 - s⟩ : ℂ).re ∧
        ((⟨(1 - s) * x0 + s * ((n : ℝ) + 1 - 3 / 4 + 1 / 2), 1 - s⟩ : ℂ).re < (n : ℝ) + 1 ∨
          0 < (⟨(1 - s) * x0 + s * ((n : ℝ) + 1 - 3 / 4 + 1 / 2), 1 - s⟩ : ℂ).im ∨
          dist (⟨(1 - s) * x0 + s * ((n : ℝ) + 1 - 3 / 4 + 1 / 2), 1 - s⟩ : ℂ) ((n + 2 : ℕ) : ℂ) < 1 / 2) := by sorry
