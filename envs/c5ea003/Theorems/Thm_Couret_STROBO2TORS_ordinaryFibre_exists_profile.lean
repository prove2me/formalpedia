-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_ordinaryFibre_exists_profile
-- name    : Couret.STROBO2TORS.ordinaryFibre_exists_profile
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:53:04.439814+00:00
-- url     : https://prove2.me/theorems/4408d503-edd5-4f1b-afcf-4ba5fc007ca2
-- title:
--   Every ordinary fibre has a profile at most three
-- statement:
--   Let $G$ be a finite abelian group, $H=\{u:2u=0\}$, and let an ordinary fibre mean a triple square fibre of size $|H|$. Its profile-j family consists of ordinary fibres containing some support S with |S∩H|=j. For every ordinary fibre F,
--
--   $$\exists j\in\mathbb N:\quad j\le3,\quad F\text{ lies in the profile-}j\text{ family}.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/c7adacbb38c59753318ef256bb966a4cd0dc0d7d/research/strobo-2tors-2026-10-12/lean/Strobo2TorsProfilePartition.lean#L27-L40, lines 27–40; source file SHA-256 d633af551e3cf27c64086b352688291b34fc31f6e6540a5de139ab273adc9a59; Typing erratum: Source grouped S with F as Finset (Finset G); hS and hj require S : Finset G. Only this binder was corrected; proof and other hypotheses unchanged.; duplicate statement Couret.STROBO2TORS.ordinaryFibresProfile_disjoint supplied by Strobo2TorsClosedHistogram after exact elaborated-type comparison; theorem Couret.STROBO2TORS.ordinaryFibre_exists_profile

import Aesop
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_ordinaryFibre_eq_orbit
import Definitions.Def_Couret_Strobo2TorsOrdinaryCount_88997e4d335a
import Definitions.Def_Couret_Strobo2TorsOrdinaryProfiles_c4120e11e59a

set_option autoImplicit false

namespace Couret.STROBO2TORS
variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]

theorem ordinaryFibre_exists_profile
    (F : Finset (Finset G))
    (hF : F ∈ (ordinaryFibres : Finset (Finset (Finset G)))) :
    ∃ j : ℕ, j ≤ 3 ∧
      F ∈ (ordinaryFibresProfile j : Finset (Finset (Finset G))) := by sorry




end Couret.STROBO2TORS
