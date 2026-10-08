-- Prove2me | Theorems.Thm_Goldbach_density_kernel_taylor_enclosure
-- name    : Goldbach.density_kernel_taylor_enclosure
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T03:30:35.186027+00:00
-- url     : https://prove2.me/theorems/7b6e5cc2-2805-4b0f-82d5-c1f6f2a31aa2
-- title:
--   A closed Taylor enclosure for the density detector Laplace kernel
-- statement:
--   Let $g(u)=(2-u)^3(4+6u+u^2)/30$ on $[0,2]$, and write its exact moments as
--
--   $$M_j=\frac{4\cdot2^{j+4}}{5(j+1)(j+2)(j+3)(j+4)}
--   +\frac{6\cdot2^{j+5}}{5(j+2)(j+3)(j+4)(j+5)}
--   +\frac{2^{j+6}}{5(j+3)(j+4)(j+5)(j+6)}.$$
--
--   For every natural number $n$ and real number $z$ with $4|z|\le n+1$,
--
--   $$\left|\int_0^2g(u)e^{-zu}\,du-
--   \sum_{j=0}^{n-1}\frac{(-z)^jM_j}{j!}\right|
--   \le\frac{16}{9}\frac{(2|z|)^n}{n!}.$$
--
--   The closed proof establishes all moment identities, positivity of the kernel,
--   and its mass $8/9$. It transfers Mathlib's complex exponential Taylor bound to
--   real arguments, bounds the pointwise remainder on the whole interval, and
--   integrates that bound. Only Mathlib is imported, with no open theorem, solution
--   import, numerical approximation, or additional axiom.
--
--   The kernel is from equation (3.21) in
--   https://arxiv.org/html/2511.05631v2#S3 . At $n=49$ this theorem supplies the
--   Taylor enclosure used by the independent rational detector audit. Evaluating
--   the resulting rational polynomial for each exported detector remains a separate
--   Python computation. The theorem does not establish the analytic density
--   inequality, any zero-position hypothesis, or a Goldbach conclusion. It
--   formalizes a known numerical-analysis step; no mathematical novelty is claimed.
-- source:
--   Taylor enclosure of the Laplace kernel in equation (3.21), https://arxiv.org/html/2511.05631v2#S3 . Uses Mathlib Complex.exp_bound and exact polynomial integration; no density-theorem verification or mathematical novelty is claimed.

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.Exponential
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false

theorem Goldbach.density_kernel_taylor_enclosure (n : ℕ) (z : ℝ) (hz : 4*|z| ≤ (n:ℝ)+1) :
    |(∫ u in (0:ℝ)..2, ((2-u)^3*(4+6*u+u^2)/30)*Real.exp (-z*u)) -
      ∑ k ∈ Finset.range n, ((-z)^k/(k.factorial:ℝ))*
        (4*(2:ℝ)^(k+4)/(5*((k:ℝ)+1)*((k:ℝ)+2)*((k:ℝ)+3)*((k:ℝ)+4)) +
         6*(2:ℝ)^(k+5)/(5*((k:ℝ)+2)*((k:ℝ)+3)*((k:ℝ)+4)*((k:ℝ)+5)) +
         (2:ℝ)^(k+6)/(5*((k:ℝ)+3)*((k:ℝ)+4)*((k:ℝ)+5)*((k:ℝ)+6)))| ≤
      (16/9:ℝ)*(2*|z|)^n/(n.factorial:ℝ) := by sorry
