-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaNearOne
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_ZetaNearOne
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:48:21.129605+00:00
-- url     : https://prove2.me/theorems/7f76857b-5e1d-454d-90b6-a023c7170321
-- title:
--   Completed zeta factors near the pole at one
-- statement:
--   Let $\zeta$ be the Riemann zeta function and let $\gamma$ be the Euler–Mascheroni constant. The completed functions $\zeta_0,\zeta_1:\mathbb C\to\mathbb C$ are defined by
--
--   $$
--   \zeta_0(s)=\begin{cases}\gamma,&s=1,\\
--   \zeta(s)-(s-1)^{-1},&s\ne1,\end{cases}
--   \qquad
--   \zeta_1(s)=1+(s-1)\zeta_0(s).
--   $$
--
--   The residue-normalized factor is $R(z)=\zeta_1(1+z)$. Near the origin, the paired factor compares $R(u+v)$ with $R(u)R(v)$ by their quotient; finite-system factors multiply these paired factors over a finite index set. The variables $s,z,u,v$ are complex. These completed expressions remove the apparent singularity of $z\zeta(1+z)$ and give the normalizations used in the sieve comparison.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/ZetaNearOne.lean#L27-L199; compatibility definitions backported from https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean

import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Lean

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

/-
The completion definitions and their differentiability proofs below are
backported from Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean at
 db584cd6d46c92f209a44c0f1c829460d327499d.
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Terence Tao
-/
section GreenTaoZetaCompatibility

open Set Filter Complex
open scoped Topology

/-- `riemannZeta₀ s` is the completion of `riemannZeta s - (s-1)⁻¹` at `s = 1`. -/
noncomputable def riemannZeta₀ (s : ℂ) : ℂ :=
  if s = 1 then (Real.eulerMascheroniConstant : ℂ) else riemannZeta s - (s-1)⁻¹

/-- `riemannZeta₁ s` is the completion of `(s-1) * riemannZeta s` at `s = 1`. -/
noncomputable def riemannZeta₁ (s : ℂ) : ℂ := 1 + (s - 1) * riemannZeta₀ s













end GreenTaoZetaCompatibility

namespace Wikipedia.SzemeredisTheorem

open Filter
open scoped BigOperators Topology

/-- The removable completion of `z * ζ(1 + z)` at `z = 0`. -/
noncomputable def zetaResidueFactor (z : ℂ) : ℂ :=
  riemannZeta₁ (1 + z)

















/-- The completed two-variable zeta quotient which tends to one when both
parameters tend to zero. -/
noncomputable def normalizedZetaPairFactor
    (u v : ℂ) : ℂ :=
  zetaResidueFactor (u + v) /
    (zetaResidueFactor u * zetaResidueFactor v)











/-! ## Finite systems of paired zeta factors -/

/-- Product of the completed pair factors for a finite family of divisor
pairs. -/
noncomputable def normalizedZetaSystemFactor
    {κ : Type*} [Fintype κ]
    (u v : κ → ℂ) : ℂ :=
  ∏ i, normalizedZetaPairFactor (u i) (v i)











end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.normalizedZetaPairFactor.eq_1,
    `Wikipedia.SzemeredisTheorem.normalizedZetaSystemFactor.eq_1,
    `Wikipedia.SzemeredisTheorem.zetaResidueFactor.eq_1,
    `riemannZeta₀.eq_1,
    `riemannZeta₁.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


