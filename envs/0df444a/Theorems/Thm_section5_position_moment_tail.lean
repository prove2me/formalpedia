-- Prove2me | Theorems.Thm_section5_position_moment_tail
-- name    : section5_position_moment_tail
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:04:21.126525+00:00
-- url     : https://prove2.me/theorems/c21e6952-5136-4054-b3de-ccc0b24c6385
-- title:
--   Tail energy controlled by the position second moment
-- statement:
--   Let $E$ be a normed additive group, let $f:\mathbb R\to E$, and let $R\ge0$. Assume that both $x\mapsto\|f(x)\|^2$ and $x\mapsto x^2\|f(x)\|^2$ are Lebesgue integrable. Then
--
--   $$R^2\int_{|x|\ge R}\|f(x)\|^2\,dx\le\int_{\mathbb R}x^2\|f(x)\|^2\,dx.$$
--
--   The estimate converts a finite position moment into a tail-energy bound for truncating a wavefunction.
-- source:
--   Original analytic auxiliary result supporting Krivcenko, Nguyen and de Wolf, https://arxiv.org/html/2609.40331v3, Section 5.1 and Appendix D. Formalization: Solutions/Section5CellQuadrature.lean, lines 178–195.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set

theorem section5_position_moment_tail {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (R : ℝ) (hR : 0 ≤ R)
    (hf : Integrable (fun x => ‖f x‖^2))
    (hm : Integrable (fun x => x^2*‖f x‖^2)) :
    R^2 * (∫ x in {x : ℝ | R ≤ |x|}, ‖f x‖^2) ≤
      ∫ x : ℝ, x^2*‖f x‖^2 := by sorry
