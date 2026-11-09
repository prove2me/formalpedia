-- Prove2me | Theorems.Thm_CouretOaiBridge01_fixedModulusNoGain
-- name    : CouretOaiBridge01.fixedModulusNoGain
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T21:02:21.744086+00:00
-- url     : https://prove2.me/theorems/135debde-1192-4ad3-bd9a-0b4e90eed6a3
-- title:
--   Fixed convolution preserves full-vector Big-O
-- statement:
--   Let U=(Z/30)^times and R[U] be its real group algebra. Write delta_u for the atom at u, tau=delta_1+delta_11+delta_29, sigma=(delta_1+delta_11+delta_29-2delta_19)/3, and Phi for coefficientwise extension from Q[U] to R[U]. Equip R[U] with the sup norm of its eight real coefficients. For any index type alpha, seminormed additive group G, F:alpha→R[U], g:alpha→G and filter l, $$(x\mapsto\tau F(x))=O_l(g)\iff F=O_l(g).$$ No finite-dimensional condition on G or nontrivial-filter premise is required.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/BRIDGE01_A2_FixedModulusNoGain.lean#L110-L122, lines 110–122; source file SHA-256 d05751252a8be9b8319eca7acb46757defdefacd59a3142c705663fd5461cbac; proof-only compatibility repair; declaration headers and elaborated theorem types preserved; theorem CouretOaiBridge01.fixedModulusNoGain

import Definitions.Def_Couret_BRIDGE01_A2_FixedModulusNoGain_7a86db44985c
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Asymptotics
import Mathlib.Data.ZMod.Units
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_CouretOaiBridge01_isBigO_comp_continuousLinearEquiv_iff
import Definitions.Def_Couret_BRIDGE01_A1_U30KernelInverse_5560f1024274
attribute [local instance] CouretOaiBridge01.u30AlgRNormedAddCommGroup
attribute [local instance] CouretOaiBridge01.u30AlgRNormedSpace

/-!
# BRIDGE01 / A2: fixed-modulus no-gain on the full real coefficient vector

RESEARCH BRANCH ONLY — NO RH CLAIM — NO NOVELTY CLAIM.
The norm is the sup norm transported from all eight coefficient coordinates.
Completeness is used only for the real scalar field in Mathlib's continuity API.
-/

open Filter
open Asymptotics

namespace CouretOaiBridge01

noncomputable section

theorem fixedModulusNoGain
    {G α : Type*}
    [SeminormedAddCommGroup G]
    (F : α → U30AlgR)
    (g : α → G)
    (l : Filter α) :
    (fun x => tauR * F x) =O[l] g ↔ F =O[l] g := by sorry


end

end CouretOaiBridge01
