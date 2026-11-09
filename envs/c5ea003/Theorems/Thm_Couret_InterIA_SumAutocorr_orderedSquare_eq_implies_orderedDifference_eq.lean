-- Prove2me | Theorems.Thm_Couret_InterIA_SumAutocorr_orderedSquare_eq_implies_orderedDifference_eq
-- name    : Couret.InterIA.SumAutocorr.orderedSquare_eq_implies_orderedDifference_eq
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:51:26.28267+00:00
-- url     : https://prove2.me/theorems/88d6f3a8-fb27-4766-a6c0-423d1e86c38e
-- title:
--   Equal cyclic sum profiles imply equal difference profiles
-- statement:
--   For a finite subset $A$ of an abelian group, let $R_A(z)=|\{(a,b)\in A^2:a+b=z\}|$. Let $n>0$ and $S,T\subseteq\mathbb Z/n\mathbb Z$. If $R_S=R_T$, then
--
--   $$|\{(a,b)\in S^2:a-b=z\}|=|\{(a,b)\in T^2:a-b=z\}|\quad\text{for every }z.$$
--
--   This converts a sum-profile collision into an autocorrelation collision.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/sum-autocorr-20261105/SumAutocorr.lean, lines 81–102; source file SHA-256 034fe0afbe3c002f93196fe2060cea425c9f8cf2da4c42c54bbcf94783bc644d; theorem Couret.InterIA.SumAutocorr.orderedSquare_eq_implies_orderedDifference_eq

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
import Theorems.Thm_Couret_InterIA_SumAutocorr_dft_pairCount
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc
import Mathlib.Analysis.Fourier.ZMod

set_option autoImplicit false
namespace Couret.InterIA.SumAutocorr
open Finset Couret.InterIA.Parity

variable {n : ℕ} [NeZero n]

theorem orderedSquare_eq_implies_orderedDifference_eq
    (S T : Finset (ZMod n)) (h : ∀ z, orderedSquare S z=orderedSquare T z) :
    ∀ z, orderedDifference S z=orderedDifference T z := by sorry




end Couret.InterIA.SumAutocorr
