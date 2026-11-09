-- Prove2me | Definitions.Def_Couret_SumAutocorr_074e6f9ba1f0
-- name    : Couret_SumAutocorr_074e6f9ba1f0
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:00:33.819758+00:00
-- url     : https://prove2.me/theorems/bf0446d4-3f2a-4e82-9bec-ede7d96b3e21
-- title:
--   Pair counts, autocorrelation and support Fourier transforms
-- statement:
--   On a nonzero finite cyclic group, for any binary operation $\circ$ define $P_{S,T}^{\circ}(z)=\#\{(a,b)\in S\times T:a\circ b=z\}$. Ordered difference counts specialize to $a\circ b=a-b$. The support Fourier transform is
--
--   $$\widehat{1_S}(k)=\sum_{a\in S}\exp(-2\pi i ak/n).$$
--
--   These definitions put sum counts, difference autocorrelation and Fourier measurements in a shared finite framework.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/sum-autocorr-20261105/SumAutocorr.lean; source file SHA-256 034fe0afbe3c002f93196fe2060cea425c9f8cf2da4c42c54bbcf94783bc644d

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

def pairCount (S T : Finset (ZMod n)) (op : ZMod n → ZMod n → ZMod n)
    (z : ZMod n) : ℕ :=
  ∑ a ∈ S, ∑ b ∈ T, if op a b=z then 1 else 0

/-- Labelled ordered differences, including all diagonal pairs at zero. -/
def orderedDifference (S : Finset (ZMod n)) (z : ZMod n) : ℕ :=
  pairCount S S (fun a b => a-b) z

noncomputable def supportFT (S : Finset (ZMod n)) (k : ZMod n) : ℂ :=
  ∑ a ∈ S, ZMod.stdAddChar (-(a*k))

















end Couret.InterIA.SumAutocorr


