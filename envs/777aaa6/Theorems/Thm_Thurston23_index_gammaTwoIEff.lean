-- Prove2me | Theorems.Thm_Thurston23_index_gammaTwoIEff
-- name    : Thurston23.index_gammaTwoIEff
-- status  : Proved
-- author  : @t4v1
-- created : 2026-09-13T16:27:55.546352+00:00
-- url     : https://prove2.me/theorems/9e79b354-697e-4b8d-ad98-c4ac57498d5f
-- title:
--   The index of $\Gamma(2+i)$ in the effective Picard group is $60$
-- statement:
--   The image of $\Gamma(2+i)$ in the effective Picard group $\mathrm{PicardEff} = \mathrm{SL}_2(\mathbb{Z}[i])/\{\pm 1\}$ has index $60$. Two facts combine. First, reduction modulo $2+i$ maps $\mathrm{SL}_2(\mathbb{Z}[i])$ onto $\mathrm{SL}_2(\mathbb{Z}[i]/(2+i)) \cong \mathrm{SL}_2(\mathbb{F}_5)$, a group of order
--
--   $$|\mathrm{SL}_2(\mathbb{F}_5)| = 5\,(5^2 - 1) = 120,$$
--
--   so $[\mathrm{SL}_2(\mathbb{Z}[i]) : \Gamma(2+i)] = 120$. Second, the kernel of the action of the Picard group on hyperbolic space is exactly $\{\pm 1\}$, and $-1 \notin \Gamma(2+i)$ since $-1 \not\equiv 1 \pmod{2+i}$; so passing to the effective quotient halves the index. The statement is what pins the covolume of $\Gamma(2+i)$ to a number: $60$ times the volume of the half box.
-- source:
--   W. P. Thurston, Three-dimensional manifolds, Kleinian groups and hyperbolic geometry, Bull. Amer. Math. Soc. 6 (1982), 357-381, Question 23 (p. 380). Formalisation: https://github.com/t4v1/thurston23/blob/58bb3fd/Thurston23.lean#L3153-L3165 (with sections IndexOfGamma and KernelPmOne).

import Definitions.Def_Thurston23_picard

namespace Thurston23

open MeasureTheory

theorem index_gammaTwoIEff : gammaTwoIEff.index = 60 := by
  sorry

end Thurston23
