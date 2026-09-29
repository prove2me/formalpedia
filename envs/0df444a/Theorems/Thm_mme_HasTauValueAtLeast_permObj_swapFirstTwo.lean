-- Prove2me | Theorems.Thm_mme_HasTauValueAtLeast_permObj_swapFirstTwo
-- name    : mme_HasTauValueAtLeast_permObj_swapFirstTwo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:30:40.536722+00:00
-- url     : https://prove2.me/theorems/22f1a120-f1b5-4ef8-b7f9-59319e8b9848
-- title:
--   Direct tau-value is invariant under swapping two tensor modes
-- statement:
--   Let $T$ be an order-three tensor over a field.  If its direct Coppersmith--Winograd $\tau$-value is at least $V$, then the tensor obtained by exchanging its first two modes also has $\tau$-value at least $V$.  A finite matrix-multiplication extraction is transported by the mode swap, which replaces every format $\langle a,b,c\rangle$ by $\langle c,b,a\rangle$ and therefore preserves the volume $abc$ and its $\tau$-weight.  The result applies to arbitrary tensors and endpoints.
-- source:
--   Standard tensor-mode invariance of the Coppersmith--Winograd value; compare A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_tau_value

open MME

universe u

set_option autoImplicit false

theorem mme_HasTauValueAtLeast_permObj_swapFirstTwo
    {K : Type u} [Field K] {T : TensorObj K 3} {tau V : ℝ}
    (h : HasTauValueAtLeast T tau V) :
    HasTauValueAtLeast
      (TensorObj.permObj swapFirstTwoPerm T) tau V := by
  sorry
