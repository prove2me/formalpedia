-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_certificate_sound
-- name    : Couret.InterIA.SingletonNecessity.certificate_sound
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:59:52.318913+00:00
-- url     : https://prove2.me/theorems/6e76ccde-6ced-42d4-9755-e3a2fdf48cb0
-- title:
--   A valid matching certificate forces a label collision
-- statement:
--   Let $G$ be an abelian group, $x:\{0,\ldots,5\}\to G$, $c$ a matching certificate, and $b$ a Boolean selecting the mixed or cross relation system. If the checker accepts $c$ and every row of the relation system selected by $b$ and the certificate permutation evaluates to zero under $x$, then $$c.i<c.j<7,\qquad L_{c.i}(x)=L_{c.j}(x).$$
--
--   Here the seven labels are the stored label vectors evaluated at $x$.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/CertificateSoundness.lean, lines 41–52; source file SHA-256 10bfe9fce95e54024ac1f979cda844bfbd42adbb9a4bcc608954b4c55b77c9f0; theorem Couret.InterIA.SingletonNecessity.certificate_sound

import Definitions.Def_Couret_CertificateSoundness_1059e04412f7
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_SingletonNecessity_evaluation_combination_zero
import Definitions.Def_Couret_MatchingCertificateCore_fbb5abd3e874
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Finset
variable {G : Type*} [AddCommGroup G]

theorem certificate_sound (mixed : Bool) (c : Certificate)
    (hc : valid mixed c = true) (x : Fin 6 → G)
    (hr : ∀ v ∈ relations mixed c.perm, evaluation x v = 0) :
    c.i < c.j ∧ c.j < 7 ∧ evaluation x (label c.i) = evaluation x (label c.j) := by sorry


end Couret.InterIA.SingletonNecessity
