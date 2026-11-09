-- Prove2me | Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedData_coverage
-- name    : Couret.InterIA.SingletonNecessity.mixedData_coverage
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:02:10.474229+00:00
-- url     : https://prove2.me/theorems/6471dd88-41ca-403a-941e-c1d6a69b1a45
-- title:
--   Mixed certificates cover every seven-term permutation
-- statement:
--   The permutation lists carried by the mixed-certificate data equal, as a list including ordering and multiplicities, all enumerated permutations of $0,\ldots,6$: $$\operatorname{map}(\operatorname{perm},\operatorname{mixedData})=\operatorname{permutations}([0,\ldots,6]).$$
--
--   This is the exhaustive coverage certificate.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/abelian-singleton-necessity-20261104/formal/MatchingCertificateData.lean, lines 6236–6236; source file SHA-256 281f2db6030f883e89d5aa00658e16116a8de5187f3c58c3d03bf50c9b44685c; theorem Couret.InterIA.SingletonNecessity.mixedData_coverage

import Definitions.Def_Couret_MatchingCertificateData_656be71337d8
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Permutation
import Definitions.Def_Couret_MatchingCertificateCore_fbb5abd3e874

set_option autoImplicit false

set_option maxRecDepth 1000000

set_option maxHeartbeats 20000000

namespace Couret.InterIA.SingletonNecessity

theorem mixedData_coverage : mixedData.map Certificate.perm = (List.range 7).permutations' := by sorry




end Couret.InterIA.SingletonNecessity
