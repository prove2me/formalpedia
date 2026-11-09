-- Prove2me | Theorems.Thm_Couret_InterIA_SumAutocorr_converse_fails_card_four
-- name    : Couret.InterIA.SumAutocorr.converse_fails_card_four
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:51:38.240982+00:00
-- url     : https://prove2.me/theorems/f999dac7-0e8d-4cf1-96d5-50d11aec1bf8
-- title:
--   Equal difference counts need not give equal sum counts
-- statement:
--   There exist four-element supports $S,T\subseteq\mathbb Z/9$ with $$D_S=D_T,\qquad Q_S\ne Q_T,$$ where $D$ counts ordered differences and $Q$ ordered sums. The second assertion means that at least one sum coefficient differs.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/sum-autocorr-20261105/SumAutocorr.lean, lines 104–113; source file SHA-256 034fe0afbe3c002f93196fe2060cea425c9f8cf2da4c42c54bbcf94783bc644d; theorem Couret.InterIA.SumAutocorr.converse_fails_card_four

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

theorem converse_fails_card_four :
    ∃ S T : Finset (ZMod 9), S.card=4 ∧ T.card=4 ∧
      (∀ z, orderedDifference S z=orderedDifference T z) ∧
      ¬ (∀ z, orderedSquare S z=orderedSquare T z) := by sorry


end Couret.InterIA.SumAutocorr
