-- Prove2me | Theorems.Thm_ModNullUniversality_haar_amplification
-- name    : ModNullUniversality.haar_amplification
-- status  : Proved
-- author  : @username
-- created : 2026-11-09T09:02:29.118822+00:00
-- url     : https://prove2.me/theorems/b11bbd4e-c710-48b4-ba44-5e07c461453b
-- title:
--   Uniform standard-Borel-target consequence of Haar amplification
-- statement:
--   Fix a compact metrizable group $K$ with normalized Haar probability and a Borel equivalence relation $F$ on a nonempty standard Borel space. There is one Borel equivalence relation $Q$ on a standard Borel space, chosen before the subgroup or domain, such that for every Borel subgroup $H\le K$ and every Borel Haar-conull $C\subseteq K$,
--
--   $$E_H^K\mathbin{\upharpoonright}C\leq_B F
--   \quad\Longrightarrow\quad E_H^K\leq_B Q.$$
--
--   This target records the uniform standard-Borel consequence of the manuscript's Lemmas 3.1–3.2. Those lemmas provide the almost-everywhere power as such a target. The statement here does not identify $Q$ with a separately formalized topological $L^0$ space. No abelian hypothesis or invariance of $C$ is imposed. The original reduction and the resulting global reduction are allowed to depend on $H$ and $C$.
-- source:
--   Universality modulo null sets in the Borel hierarchy, user-supplied unpublished manuscript dated 9 November 2026; SHA-256 48745c75427f83370292c2e4cf91ec06377e80472252db0182599edcd05e2d97, Lemmas 3.1–3.2, lines 135–236, specifically the uniform target consequence in lines 218–220. The source almost-everywhere power is also discussed by B. Tsirelson, arXiv:math/0508414, Section 1, p. 3. https://arxiv.org/abs/math/0508414

import Definitions.Def_ModNullCompact20261109

set_option autoImplicit false

theorem ModNullUniversality.haar_amplification
    (K : ModNullUniversality.CompactMetrizableHaarGroup)
    (F : ModNullUniversality.StandardBorelEquivalence)
    (hF : Nonempty F.Carrier) :
    ∃ Q : ModNullUniversality.StandardBorelEquivalence,
      ∀ H : Subgroup K.Carrier, MeasurableSet (H : Set K.Carrier) →
        ∀ C : Set K.Carrier, MeasurableSet C → K.haar C = 1 →
          ModNullUniversality.BorelReducible
            (fun x y : C => ModNullUniversality.CosetRelation K H x.val y.val) F.rel →
          ModNullUniversality.BorelReducible (ModNullUniversality.CosetRelation K H) Q.rel := by sorry
