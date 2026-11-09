-- Prove2me | Theorems.Thm_Couret_InterIA_SumAutocorr_dft_pairCount
-- name    : Couret.InterIA.SumAutocorr.dft_pairCount
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:38:35.68637+00:00
-- url     : https://prove2.me/theorems/5c9a2471-8128-4471-8b3a-1bfd88762e6e
-- title:
--   Fourier transform of an arbitrary pair-count operation
-- statement:
--   Let $n>0$, $S,T\subseteq\mathbb Z/n\mathbb Z$, and let $\circ$ be any binary operation on this group. Put $P(z)=\#\{(a,b)\in S\times T:a\circ b=z\}$. For each $k\in\mathbb Z/n\mathbb Z$,
--
--   $$\widehat P(k)=\sum_{a\in S}\sum_{b\in T}\exp(-2\pi i(a\circ b)k/n).$$
--
--   The Fourier transform is unnormalized. This identity applies without algebraic assumptions on the operation.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/sum-autocorr-20261105/SumAutocorr.lean, lines 31–46; source file SHA-256 034fe0afbe3c002f93196fe2060cea425c9f8cf2da4c42c54bbcf94783bc644d; theorem Couret.InterIA.SumAutocorr.dft_pairCount

import Definitions.Def_Couret_SumAutocorr_074e6f9ba1f0
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc
import Mathlib.Analysis.Fourier.ZMod

set_option autoImplicit false
namespace Couret.InterIA.SumAutocorr
open Finset Couret.InterIA.Parity

variable {n : ℕ} [NeZero n]

theorem dft_pairCount (S T : Finset (ZMod n))
    (op : ZMod n → ZMod n → ZMod n) (k : ZMod n) :
    ZMod.dft (fun z => (pairCount S T op z : ℂ)) k =
      ∑ a ∈ S, ∑ b ∈ T, ZMod.stdAddChar (-(op a b*k)) := by sorry












end Couret.InterIA.SumAutocorr
