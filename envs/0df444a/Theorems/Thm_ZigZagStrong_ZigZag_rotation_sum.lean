-- Prove2me | Theorems.Thm_ZigZagStrong_ZigZag_rotation_sum
-- name    : ZigZagStrong.ZigZag.rotation_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:04:58.787609+00:00
-- url     : https://prove2.me/theorems/23524051-398c-4680-95bd-1faf1edc30bb
-- title:
--   Claim 3.9 — rotation as a port-operator sum
-- statement:
--   Let $\Gamma$ have finite symmetric generating set $S$ and act on a possibly infinite set $V$. With $E_{s,t}e_s=e_t$, rotation on the actual space $\ell^2(S)\otimes\ell^2(V)$ satisfies
--   $$\dot G_\pi=\sum_{s\in S}E_{s,s^{-1}}\otimes\pi(s).$$
--   The left side is defined coordinatewise from rotation. This identity provides its matrix-polynomial representation for arbitrary group actions.
--
--   Differences from the source:
--   - encoding: Hilbert tensor product with a finite port factor → Finite Hilbert direct sum PiLp 2; reason: The canonical unitary identification preserves the operator, not merely its norm.
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), Claim 3.9, p. 13.

import Definitions.Def_ZigZagStrong_ZigZag_Covers

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag
open Filter MeasureTheory
open scoped BigOperators Topology

theorem rotation_sum {Γ V : Type*} [Group Γ] {d : ℕ} (S : Generators Γ d)
  (π : Γ →* Equiv.Perm V) :
  rotation S.flip (fun i => permL2 (π (S.gen i))) =
    ∑ i : Fin d, StrongConv.tensorOp (elementary i (S.flip i)) (permL2 (π (S.gen i))) := by sorry

end ZigZagStrong.ZigZag
