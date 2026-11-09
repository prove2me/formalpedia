-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_support_probe_sq
-- name    : Couret.STROBO2TORS.recoh_support_probe_sq
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:49:07.209039+00:00
-- url     : https://prove2.me/theorems/b33629ca-3301-41f5-9c41-3c3a3b653d75
-- title:
--   The square of a character reading is determined by square counts
-- statement:
--   Let $G$ be a finite abelian group. For a character $\chi:G\to\mathbb C$ write $P_\chi(S)=\sum_{x\in S}\chi(x)$, and for a bank $(\chi_i)$ write $\operatorname{Obs}(S)=(Q_S,(P_{\chi_i}(S))_i)$, where $Q_S(z)$ counts ordered pairs from $S$ summing to $z$. The exact decoder of $(R,o)$ consists of all three-element supports $S$ with $\operatorname{Obs}(S)=(R,o)$. For any finite support $S$ and complex character $\chi$,
--
--   $$P_\chi(S)^2=\sum_{z\in G}Q_S(z)\chi(z).$$
--
--   No cardinality restriction on $S$ is needed. This links Fourier probes to ordered-square data.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohSquareFourier.lean, lines 19–45; source file SHA-256 d945a6e2f58d516ec42667f54f80235d5d7aef6c8722194abaf14ac9355633e8; theorem Couret.STROBO2TORS.recoh_support_probe_sq

import Aesop
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

set_option autoImplicit false

/-!
The actual ordered convolution square determines the square of every
individual labelled complex character coefficient.  This is a finite-sum
identity for arbitrary supports, independent of the triple classification.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem recoh_support_probe_sq (chi : AddChar G ℂ) (S : Finset G) :
    (recohSupportProbe chi S) ^ 2 =
      ∑ z : G, (orderedSquare S z : ℂ) * chi z := by sorry






end Couret.STROBO2TORS
