-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_exists_norm_normalizedZetaSystemFactor_sub_one_lt
-- name    : Wikipedia.SzemeredisTheorem.exists_norm_normalizedZetaSystemFactor_sub_one_lt
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:55:40.178823+00:00
-- url     : https://prove2.me/theorems/a691162b-0a2b-4e42-b93e-e71e0ccb7f50
-- title:
--   An epsilon-delta bound for the normalized zeta-system factor
-- statement:
--   For every finite index type $\kappa$ and $\varepsilon>0$, there is $\delta>0$ such that complex coordinate vectors $u,v$ with sup norms below $\delta$ satisfy $\|\operatorname{normalizedZetaSystemFactor}(u,v)-1\|<\varepsilon$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/ZetaNearOne.lean#L256-L277

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

theorem Wikipedia.SzemeredisTheorem.exists_norm_normalizedZetaSystemFactor_sub_one_lt
    {κ : Type*} [Fintype κ]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ u v : κ → ℂ,
        ‖u‖ < δ →
        ‖v‖ < δ →
        ‖normalizedZetaSystemFactor u v - 1‖ < ε := by sorry
