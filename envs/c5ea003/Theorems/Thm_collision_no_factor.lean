-- Prove2me | Theorems.Thm_collision_no_factor
-- name    : collision_no_factor
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-10T13:16:36.143042+00:00
-- url     : https://prove2.me/theorems/b025a553-ff07-460d-866a-39efdf079ee3
-- title:
--   An observation collision with different verdicts prevents factorization
-- statement:
--   For arbitrary types $H,O,V$, let $p:H\to O$ and $v:H\to V$. If $a,b\in H$ satisfy $p(a)=p(b)$ and $v(a)\ne v(b)$, then
--
--   $$\neg\exists r:O\to V,\;\forall h,\;v(h)=r(p(h)).$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/CAUSAL-PAIR-01/blob/02bcbbf17dfaade51171885578a228b16736d425/causal_fiber_01/CausalFiber01.lean#L16-L22; source SHA-256 bcff7eeabd153cd20f42ccd810dd20c074c9a899271ba5d29a4d6ed056b197ad; theorem collision_no_factor

import Definitions.Def_Couret_CausalFiber01_c81331552304
import Theorems.Thm_factor_implies_fiber_constant
/-! CAUSAL-FIBER-01: toy model; not a production FCI proof. -/
universe u v w

theorem collision_no_factor
    {H : Type u} {O : Type v} {V : Type w}
    (p : H → O) (v : H → V)
    (a b : H) (same : p a = p b) (different : v a ≠ v b) :
    ¬ ∃ r : O → V, ∀ h, v h = r (p h) := by sorry































/- Conservative authorization is weaker than exact verdict reconstruction.
   The observation map and the permitted-history predicate must be justified
   independently when connecting this theorem to a verifier. -/






/- CAUSAL-PAIR-01 bridge: one quiescent operation, initial effects 0 or 1,
   restored empty receipt ledger, non-idempotent receiver. This finite model
   is linked to measured SQLite traces by bridge.py, not by a refinement proof. -/
namespace Recovery



















end Recovery
