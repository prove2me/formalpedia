-- Prove2me | Theorems.Thm_ZigZagStrong_ZigZag_involution_strong_convergence
-- name    : ZigZagStrong.ZigZag.involution_strong_convergence
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-16T07:06:45.93329+00:00
-- url     : https://prove2.me/theorems/be9b4724-39df-4927-be0d-414865bc0beb
-- title:
--   Theorem 2.4 (involution case) — strong convergence of independent uniform random involutions
-- statement:
--   Let $r \ge 0$. For each $n$, let $\tau_1, \dots, \tau_r$ be independent uniform involutions of $\{1, \dots, n+2\}$ (permutations with $\tau_i^2 = 1$; fixed points allowed), and let $u_n = (u_{n,1}, \dots, u_{n,r})$ be their permutation operators restricted to the orthogonal complement $\mathbf 1^\perp$ of the constant vectors in $\mathbb C^{n+2}$. Let $\lambda = (\lambda(a_1), \dots, \lambda(a_r))$ be the left-regular operators on $\ell^2(\mathbb Z_2^{*r})$ of the free generators $a_i$ of the free product of $r$ copies of $\mathbb Z_2$. Then for every noncommutative $*$-polynomial $P$ in $r$ variables with scalar coefficients and every $\varepsilon > 0$,
--   $$\Pr\big[\,\big|\|P(u_n, u_n^*)\| - \|P(\lambda, \lambda^*)\|\big| > \varepsilon\,\big] \longrightarrow 0 \qquad (n \to \infty).$$
--
--   This is the third of the three random models in Theorem 2.4 of Maor and Dogon, stated on its own: the conjunction `ZigZagStrong.ZigZag.random_model_strong_convergence` follows from it together with the permutation and perfect-matching cases, which are consequences of `DerandSq.theorem_2_14` (Bordenave–Collins).
--
--   **Formalization note.** Everything is in the encoding of `ZigZagStrong.ZigZag.random_model_strong_convergence`: the law is the normalized count `finiteLaw` on `Fin r → Involution (n+2)`, the limit is `regularL2 (involutionGenerator i)` on `L2 (FreeInvolutions r)`, and strong convergence is `StrongConvergence` (convergence in probability of every norm $\|P\|$, $P$ a `StrongConv.NCPoly 1 r`). Sizes are $n + 2$, as in that statement.
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), p. 9, Theorem 2.4, the case of uniform involutions; the third conjunct of ZigZagStrong.ZigZag.random_model_strong_convergence, stated on its own

import Definitions.Def_ZigZagStrong_ZigZag_Models

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag
open Filter MeasureTheory
open scoped BigOperators Topology

theorem involution_strong_convergence (r : ℕ) :
    StrongConvergence (fun n => finiteLaw (Ω := Fin r → Involution (n+2)))
      (fun _ τ i => StrongConv.permOpPerp (τ i).val)
      (fun i => regularL2 (involutionGenerator i)) := by sorry

end ZigZagStrong.ZigZag
