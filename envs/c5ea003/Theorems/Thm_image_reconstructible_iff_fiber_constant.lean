-- Prove2me | Theorems.Thm_image_reconstructible_iff_fiber_constant
-- name    : image_reconstructible_iff_fiber_constant
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-10T13:16:36.145793+00:00
-- url     : https://prove2.me/theorems/a225aaa5-7a9f-4f0d-8f02-9218da2ffc5e
-- title:
--   Reconstruction on the observation image is equivalent to fibre constancy
-- statement:
--   For arbitrary types $H,O,V$ and maps $p:H\to O$, $v:H\to V$, the following are equivalent: $v$ is constant on every fibre of $p$; and there exists a reconstructor that takes $o\in O$ together with a witness that $o$ lies in the image of $p$, and returns $v(h)$ when applied to $p(h)$ and its image witness. Reconstruction is required only on the image, with no inhabitance assumption on $V$.
-- source:
--   Alexandre Couret, https://github.com/alexcour/CAUSAL-PAIR-01/blob/02bcbbf17dfaade51171885578a228b16736d425/causal_fiber_01/CausalFiber01.lean#L29-L49; source SHA-256 bcff7eeabd153cd20f42ccd810dd20c074c9a899271ba5d29a4d6ed056b197ad; theorem image_reconstructible_iff_fiber_constant

import Definitions.Def_Couret_CausalFiber01_c81331552304
/-! CAUSAL-FIBER-01: toy model; not a production FCI proof. -/
universe u v w

theorem image_reconstructible_iff_fiber_constant
    {H : Type u} {O : Type v} {V : Type w}
    (p : H → O) (v : H → V) :
    ImageReconstructible p v ↔ FiberConstant p v := by sorry



























/- Conservative authorization is weaker than exact verdict reconstruction.
   The observation map and the permitted-history predicate must be justified
   independently when connecting this theorem to a verifier. -/






/- CAUSAL-PAIR-01 bridge: one quiescent operation, initial effects 0 or 1,
   restored empty receipt ledger, non-idempotent receiver. This finite model
   is linked to measured SQLite traces by bridge.py, not by a refinement proof. -/
namespace Recovery



















end Recovery
