-- Prove2me | Definitions.Def_Zeta23_LinAlg_Sylvester
-- name    : Zeta23_LinAlg_Sylvester
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:00:29.4695+00:00
-- url     : https://prove2.me/theorems/7371846a-87f3-48da-af2f-9b2b58749c0c
-- title:
--   The Hermitian form $x \mapsto \operatorname{Re}(x^{H}Ax)$ and positive-definiteness on a subspace
-- statement:
--   This bundle provides the two definitions on which the subspace form of Sylvester's law of inertia is stated. For an $n \times n$ matrix $A$ over $\mathbb{K} = \mathbb{R}$ or $\mathbb{C}$:
--
--   - `hermForm A` is the real-valued Hermitian form
--   $$x \;\longmapsto\; \operatorname{Re}\bigl(\overline{x} \cdot (A x)\bigr) = \operatorname{Re}(x^{H} A x),$$
--   defined for vectors $x \in \mathbb{K}^n$;
--   - `PosDefOn A W` asserts that the subspace $W \subseteq \mathbb{K}^n$ is one on which this form is positive definite: for every $x \in W$ with $x \neq 0$ one has $\operatorname{Re}(x^{H}Ax) > 0$.
--
--   The surrounding module proves that any subspace on which `hermForm A` is positive definite has dimension at most the positive index $n_+(A)$ — the engine behind [lem:inertia] (pulling back a Hermitian form cannot increase its positive index). This is the inertia input to the matrix-variational argument of paper §3, which forces many zeros onto the critical line from a two-trace comparison of the mollified Gram matrix.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/LinAlg/Sylvester.lean, docstring tag [lem:inertia]

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The linear algebra of §3 of the paper (Hermitian positive/negative parts, inertia, the positive index,
von Neumann's trace inequality, the rank–trace inequality, Weyl's perturbation bound). These seven files
were written first as a self-contained development (namespace `RHLinalg`) accompanying §3 of the paper, by the
paper's authors, and are incorporated here unchanged; they have no upstream outside this project (see README
§ Provenance and attribution).
-/

/-!
# Sylvester's law of inertia for Hermitian matrices (subspace bound)

We prove the key inequality: any subspace `W ⊆ 𝕜ⁿ` on which the Hermitian
form `x ↦ Re(xᴴAx)` is positive definite has dimension at most
`posIndex hA`.

The proof is short: `A = A₊ − A₋` with both parts PSD (`HermitianPosPart`).
If `A₊ · x = 0` for `x ∈ W ∖ {0}`, then `xᴴAx = −xᴴA₋x ≤ 0`, contradicting
positive-definiteness on `W`. So `(A₊ *ᵥ ·)|_W` is injective, hence
`dim W ≤ rank A₊ = posIndex hA`.

This is the engine behind `lem:inertia`: pulling back a Hermitian form
cannot increase its positive index.
-/

noncomputable section

open Matrix Finset Submodule
open scoped ComplexOrder

namespace RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Hermitian form `x ↦ Re(star x ⬝ (A *ᵥ x))` associated to a matrix. -/
def hermForm (A : Matrix n n 𝕜) (x : n → 𝕜) : ℝ :=
  RCLike.re (star x ⬝ᵥ (A *ᵥ x))

/-- `W` is a subspace on which `hermForm A` is positive definite. -/
def PosDefOn (A : Matrix n n 𝕜) (W : Submodule 𝕜 (n → 𝕜)) : Prop :=
  ∀ x ∈ W, x ≠ 0 → 0 < hermForm A x














end RHLinalg


