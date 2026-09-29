-- Prove2me | Theorems.Thm_LeblRA_absolute_value_polynomials
-- name    : LeblRA.absolute_value_polynomials
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-06T02:04:19.383752+00:00
-- url     : https://prove2.me/theorems/b059589d-e485-4239-9c18-220b394a86cf
-- title:
--   Corollary 11.7.4 — Absolute-value approximation with zero constant term
-- statement:
--   Let $a\ge0$ be real. There is a sequence of real polynomials satisfying
--   $$
--   \forall n\in\mathbb N,\qquad p_n(0)=0,
--   $$
--   and
--   $$
--   \forall\varepsilon>0\;\exists N\;\forall n\ge N\;\forall x\in[-a,a],
--   \qquad |p_n(x)-|x||<\varepsilon.
--   $$
--
--   Thus absolute value can be approximated uniformly while requiring every approximant to have zero constant term. This normalization is the content of [Lebl’s Corollary 11.7.4](https://www.jirka.org/ra/html/sec_stoneweier.html).
--
--   **Formalization Note.** The equation at zero holds at every index, including index zero, not merely in the limit. The value $a=0$ is allowed. No positivity, evenness, degree bound, or convergence outside the interval is imposed on the approximating polynomials.
-- source:
--   Jiří Lebl, Basic Analysis II, Section 11.7, Corollary 11.7.4. Author-hosted HTML: https://www.jirka.org/ra/html/sec_stoneweier.html (accessed 2026-09-05). The algebra conventions are Definitions 11.7.5, 11.7.7, and 11.7.15; no unit is assumed.

import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Algebra.NonUnitalAlgebra
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
open Set Filter Topology
open scoped ContinuousMapZero
open scoped Polynomial

namespace LeblRA
theorem absolute_value_polynomials (a : ℝ) (ha : 0 ≤ a) :
    ∃ p : ℕ → ℝ[X], (∀ n, (p n).eval 0 = 0) ∧
      TendstoUniformly (fun n (x : Set.Icc (-a) a) => (p n).eval (x : ℝ))
        (fun x : Set.Icc (-a) a => |(x : ℝ)|) atTop := by sorry
end LeblRA
