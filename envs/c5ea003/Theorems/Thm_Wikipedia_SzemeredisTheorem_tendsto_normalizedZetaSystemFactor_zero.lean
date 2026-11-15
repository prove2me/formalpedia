-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_tendsto_normalizedZetaSystemFactor_zero
-- name    : Wikipedia.SzemeredisTheorem.tendsto_normalizedZetaSystemFactor_zero
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:33:54.052697+00:00
-- url     : https://prove2.me/theorems/93afa7d5-c22b-484f-a894-2c533435607f
-- title:
--   The normalized zeta-system factor tends to one at the origin
-- statement:
--   For any finite index type $\kappa$, the normalized zeta-system factor on two complex coordinate vectors tends to $1$ as both vectors tend to zero.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/ZetaNearOne.lean#L208-L243

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaNearOne
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Uniform zeta control near the pole at one

Mathlib completes the singular function

`z ↦ z * riemannZeta (1 + z)`

across `z = 0` by means of the entire function `riemannZeta₁`.  This file
packages that completion in the coordinates used by the
Goldston--Yıldırım argument.  In particular, the completed residue factor
is uniformly close to one on a small complex ball, and the corresponding
two-variable normalized zeta ratio is uniformly close to one on a small
polydisc.

The latter is the stable way to state the zeta comparison: all apparent
singularities have already been removed.  Separate lemmas recover the raw
zeta expressions away from zero.
-/
open Wikipedia.SzemeredisTheorem
open Filter
open scoped BigOperators Topology
/-! ## Finite systems of paired zeta factors -/

theorem Wikipedia.SzemeredisTheorem.tendsto_normalizedZetaSystemFactor_zero
    {κ : Type*} [Fintype κ] :
    Tendsto
      (fun z : (κ → ℂ) × (κ → ℂ) =>
        normalizedZetaSystemFactor z.1 z.2)
      (𝓝 (0, 0)) (𝓝 1) := by sorry
