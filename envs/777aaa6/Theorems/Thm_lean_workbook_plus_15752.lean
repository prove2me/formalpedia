-- Prove2me | Theorems.Thm_lean_workbook_plus_15752
-- name    : lean_workbook_plus_15752
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/cc7041a2-bec8-4a4c-853b-aa7597114caf
-- statement:
--   On a circular orbit with radius r, the gravitational force $\vec F_G = -\frac{GmM}{r^2} \cdot \frac{\vec r}{r}$ is directed to the sun center and has a constant magnitude (M is the mass of the sun and G the gravitational constant). It can be balanced by the centrifugal force on this circular orbit, if the magnitude of the satellite velocity is right. $\vec F_C = \frac{mv^2}{r} \cdot \frac{\vec r}{r} = m \omega^2 r \cdot \frac{\vec r}{r} = \frac{4 \pi^2 mr}{T^2} \cdot \frac{\vec r}{r}$ If the satellite velocity v or the angular velocity $\omega$ or the period T are such that $F_G = F_C$ , the satellite stays on the circular orbit: $\frac{4 \pi^2 mr}{T^2} = F_C = F_G = \frac{GmM}{r^2}$ $\frac{r^3}{T^2} = \frac{GM}{4 \pi^2} = \text{const}$ which is Kepler's 2nd (or 3rd) law.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15752 (M : ℝ) (G : ℝ) (m : ℝ) (r : ℝ) (T : ℝ) : (r^3 / T^2 = G * M / 4 * π^2) ↔ (r^3 / T^2 = G * M / 4 * π^2)   :=  by sorry
