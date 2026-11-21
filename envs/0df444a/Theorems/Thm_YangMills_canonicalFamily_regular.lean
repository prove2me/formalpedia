-- Prove2me | Theorems.Thm_YangMills_canonicalFamily_regular
-- name    : YangMills.canonicalFamily_regular
-- status  : Open
-- author  : @LG
-- created : 2026-11-20T17:33:12.26139+00:00
-- url     : https://prove2.me/theorems/1b43b2ba-d340-4e90-9186-ddee6ed922dc
-- title:
--   Wilson regularity of the canonical Wilson lattice family
-- statement:
--   The canonical Wilson lattice family of a compact matrix gauge group $G$ satisfies Wilson regularity. Concretely: (i) the running bare coupling obeys $\beta(N,p)/\log(1/\mathrm{mesh}(N))\to s$ for some $s>0$, uniformly in the volume index $p$; (ii) every insertion is a continuous function of the link variables; (iii) every insertion is invariant under lattice gauge transformations; and (iv) each insertion token is supported on one fixed finite lattice stencil, independent of the spacing and volume. For the canonical family the mesh is $1/(N+1)$ and $\beta(N,p)=\log(N+1)$, so the slope is $s=1$; the insertions are finite products of plaquette traces, which are continuous, gauge-invariant and supported on the finitely many links of the plaquettes at the insertion site.
--
--   **Formalization Note.** This is the lattice-kinematics half of the joint-existence decomposition; it is a concrete, elementary verification about the explicit `YangMills.canonicalFamily`, independent of the continuum construction.
-- source:
--   https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/3456e5e75cf8d4cd558955a5c7638fba2d68f464/ChallengeSpec.lean (WilsonRegularity); Wilson 1974 Phys. Rev. D 10 2445; Osterwalder-Seiler 1978 Ann. Phys. 110

import Definitions.Def_YM_canonicalFamily

namespace YangMills
theorem canonicalFamily_regular (g : GaugeGroup) : WilsonRegularity (canonicalFamily g) := by sorry
end YangMills
