-- Prove2me | Theorems.Thm_WignerSemicircle_semicircleMoment_convolution
-- name    : WignerSemicircle.semicircleMoment_convolution
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:23:38.862415+00:00
-- url     : https://prove2.me/theorems/9a9544dd-b26f-4663-95c3-9dd26cc78df5
-- title:
--   Catalan convolution recursion for the semicircle moments.
-- statement:
--   **Catalan convolution recursion for the semicircle moments.**  Decomposing a
--   closed walk at its first return to the origin gives
--   `m_{2(k+1)} = ∑_{i ≤ k} m_{2i} m_{2(k-i)}`.
--
--   ```lean
--   theorem WignerSemicircle.semicircleMoment_convolution(k : ℕ) :
--       semicircleMoment (2 * (k + 1))
--         = ∑ i ∈ Finset.range (k + 1), semicircleMoment (2 * i) * semicircleMoment (2 * (k - i)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/WignerSemicircleRecursion.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/WignerSemicircleRecursion.lean#L28

-- Thm stub generated from Probability/WignerSemicircleRecursion.lean
import Mathlib
import Definitions.Def_Probability_WignerSemicircleMoments
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# The semicircle law as the unique fixed point of the moment convolution

The even moments `m_{2k} = ∫ x^{2k} dσ(x)` of the semicircle law satisfy the
*Catalan convolution recursion*

  `m_{2(k+1)} = ∑_{i=0}^{k} m_{2i} · m_{2(k-i)}`,

which is the combinatorial shadow of the Stieltjes fixed-point equation
`m(z) = 1 / (-z - m(z))` for the semicircle transform.  This recursion is exactly
the moment-method identity produced by decomposing a closed `2(k+1)`-walk at the
first return to its starting point.

We prove the recursion, and — more importantly — its converse: the recursion
together with the normalisation `m_0 = 1` **determines** the whole even moment
sequence.  Hence any limiting spectral distribution whose moments obey the
first-return decomposition must be the semicircle law: this is the abstract
uniqueness half of the moment method for Wigner matrices.
-/

open BigOperators Finset

open WignerSemicircle

theorem WignerSemicircle.semicircleMoment_convolution(k : ℕ) :
    semicircleMoment (2 * (k + 1))
      = ∑ i ∈ Finset.range (k + 1), semicircleMoment (2 * i) * semicircleMoment (2 * (k - i)) := by sorry
