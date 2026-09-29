-- Prove2me | Definitions.Def_mme_stothers_phi233_cyclic_finsets
-- name    : mme_stothers_phi233_cyclic_finsets
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-02T22:39:01.356122+00:00
-- url     : https://prove2.me/theorems/19041873-b456-4a32-9797-93aff5fcf6da
-- title:
--   Finite exact and ambient cyclic families for $\varphi_{233}$
-- statement:
--   This module equips the finite $\varphi_{233}$ profile-address types and their threefold cyclic products with explicit finite enumerations. It then defines $A_{\mathrm{cyc}}$ as the full same-marginal ambient cyclic family and $T_{\mathrm{cyc}}$ as the image of every exact-profile cyclic edge under the natural inclusion.
--
--   These are the concrete finite target and ambient families to which the affine Salem--Spencer retention and target--ambient collision bounds are applied.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Lemma 5.1(v), pp. 356--360 and 365--366, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_ambient_data

open MME

namespace MME.StothersFourth.Phi233

set_option autoImplicit false

/-- A concrete finite enumeration of all three-mode words. -/
noncomputable def profileAddressFintype (N : ℕ) :
    Fintype (ProfileAddress N) :=
  Pi.instFintype

/-- A concrete finite enumeration of the same-marginal completion family. -/
noncomputable def marginalAddressFintype
    (N alpha beta gamma delta : ℕ) :
    Fintype (MarginalAddress N alpha beta gamma delta) :=
  @Subtype.fintype _ _ (Classical.decPred _) (profileAddressFintype N)

/-- A concrete finite enumeration of the exact-profile target family. -/
noncomputable def exactProfileAddressFintype
    (N alpha beta gamma delta : ℕ) :
    Fintype (ExactProfileAddress N alpha beta gamma delta) :=
  @Subtype.fintype _ _ (Classical.decPred _)
    (marginalAddressFintype N alpha beta gamma delta)

/-- A concrete finite enumeration of the cyclic ambient edge type. -/
noncomputable def cyclicAmbientEdgeFintype
    (N alpha beta gamma delta : ℕ) :
    Fintype (CyclicAmbientEdge N alpha beta gamma delta) := by
  letI := marginalAddressFintype N alpha beta gamma delta
  unfold CyclicAmbientEdge
  infer_instance

/-- A concrete finite enumeration of the cyclic exact edge type. -/
noncomputable def cyclicExactEdgeFintype
    (N alpha beta gamma delta : ℕ) :
    Fintype (CyclicExactEdge N alpha beta gamma delta) := by
  letI := exactProfileAddressFintype N alpha beta gamma delta
  unfold CyclicExactEdge
  infer_instance

/-- The full same-marginal ambient cyclic family. -/
noncomputable def ambientFinset
    (N alpha beta gamma delta : ℕ) :
    Finset (CyclicAmbientEdge N alpha beta gamma delta) := by
  letI := cyclicAmbientEdgeFintype N alpha beta gamma delta
  exact Finset.univ

/-- The exact-profile cyclic target, embedded in the ambient edge type. -/
noncomputable def targetFinset
    (N alpha beta gamma delta : ℕ) :
    Finset (CyclicAmbientEdge N alpha beta gamma delta) := by
  letI := cyclicExactEdgeFintype N alpha beta gamma delta
  classical
  exact Finset.univ.map (exactEmbedding N alpha beta gamma delta)

end MME.StothersFourth.Phi233


