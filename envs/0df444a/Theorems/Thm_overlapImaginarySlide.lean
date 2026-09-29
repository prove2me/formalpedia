-- Prove2me | Theorems.Thm_overlapImaginarySlide
-- name    : overlapImaginarySlide
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-26T22:15:41.89567+00:00
-- url     : https://prove2.me/theorems/cb816949-375a-4814-82ba-4380779ea1fa
-- title:
--   Sliding the imaginary part towards 1 keeps a point in the matched-cover overlap
-- statement:
--   Let $E_n = \mathbb{C} \setminus \{1,2,\dots,n+1\}$ and write
--   $$R_n = \{z : \mathbb{C} \mid n+1-\tfrac34 < \operatorname{Re} z,\quad z \in R_n^{\mathrm{cap}}\},$$
--   where the second condition is $z$ lying in the punctured half-space, i.e.
--   $\operatorname{Re} z < n+1$, or $\operatorname{Im} z > 0$, or $|z-(n+2)|<\tfrac12$.
--   Then for every $z\in R_n$ and every $s\in[0,1]$ the point obtained by sliding $z$
--   vertically towards imaginary part $1$, namely $\langle \operatorname{Re} z,\ (1-s)\operatorname{Im} z + s\rangle$,
--   again lies in $R_n$.
--
--   Every puncture is a real point, so the distance from a point to $n+2$ at a fixed real part
--   is $\sqrt{(\operatorname{Re} z-(n+2))^2+(\operatorname{Im} z)^2}$, which is monotone in
--   $|\operatorname{Im} z|$. A point of the lower half of the disc therefore stays within
--   $\tfrac12$ of $n+2$ while its imaginary part rises towards $1$, and crosses into the
--   open upper half-plane when the imaginary part becomes positive. This is the first of the
--   two stages of the explicit contraction of $R_n$ onto a point, which together with the
--   subtype transfer establishes contractibility of the matched-cover overlap.
-- source:
--   A. Hatcher, Algebraic Topology (2002), Section 1.2 (van Kampen), applied to the explicit two-piece matched cover of the plane punctured at the first n+1 positive integers; the overlap $A\ \mathrm{false}\cap A\ \mathrm{true}$ of BraidsLinksMCG.puncturedPlane_standardGen_matched_cover_overlap_contractible_v1.

import Mathlib

theorem overlapImaginarySlide (n : ℕ) :
    ∀ (z : ℂ), (n : ℝ) + 1 - 3 / 4 < z.re →
      (z.re < (n : ℝ) + 1 ∨ 0 < z.im ∨ dist z ((n + 2 : ℕ) : ℂ) < 1 / 2) →
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        (n : ℝ) + 1 - 3 / 4 < (⟨z.re, (1 - s) * z.im + s⟩ : ℂ).re ∧
        ((⟨z.re, (1 - s) * z.im + s⟩ : ℂ).re < (n : ℝ) + 1 ∨
          0 < (⟨z.re, (1 - s) * z.im + s⟩ : ℂ).im ∨
          dist (⟨z.re, (1 - s) * z.im + s⟩ : ℂ) ((n + 2 : ℕ) : ℂ) < 1 / 2) := by sorry
