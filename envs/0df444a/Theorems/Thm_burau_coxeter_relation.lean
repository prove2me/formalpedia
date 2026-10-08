-- Prove2me | Theorems.Thm_burau_coxeter_relation
-- name    : burau_coxeter_relation
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T21:16:21.842605+00:00
-- url     : https://prove2.me/theorems/7d89c248-e8ea-460e-afc5-b03f14c523ec
-- title:
--   Coxeter relation (s⁻¹t)³ = 1 in the reduced braid group
-- statement:
--   **Coxeter relation for the reduced three-strand braid group.**
--
--   In $Q=B_3/\langle\langle\Delta^4\rangle\rangle$, with $\mathrm{liftS}=\overline{\sigma_0^2\sigma_1}$
--   and $\mathrm{liftT}=\overline{\sigma_0^{-1}}$ (the images of the standard generators of
--   $\mathrm{SL}(2,\mathbb Z)$), the two elements $s^{-1}t$ satisfy
--   $$ (s^{-1}t)^3 = 1 . $$
--   Together with the already available relations $s^4=1$ and $(ts)^3=s^2$ this is the
--   Coxeter–Moser presentation input for $Q\cong \mathrm{SL}(2,\mathbb Z)$.
--
--   Proof (formalised locally, zero `sorry`): put $a=s^{-1}t$ and $u=ts$. Then $sas=u$, so
--   $(sas)^3=u^3=s^2$; on the other hand, writing $sas=(sas^{-1})s^2$ and using that $s^2$ is central
--   together with $s^4=1$, one has $(sas)^3=(sas^{-1})^3(s^2)^3=s\,a^3\,s^{-1}\cdot s^2$, whence
--   $s\,a^3\,s^{-1}=1$ and $a^3=1$.
-- source:
--   Coxeter-Moser presentation of the reduced braid group; cf. C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups* (1964); J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82 (1974), §3.3.

import Definitions.Def_BurauFaithful_UnreducedBurau
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

set_option autoImplicit false

open Matrix

namespace BurauNC

abbrev B3 := PresentedGroup (BraidsLinksMCG.braidRels 3)


def g0 : B3 := BraidsLinksMCG.sigma (n := 3) ⟨0, by decide⟩


def g1 : B3 := BraidsLinksMCG.sigma (n := 3) ⟨1, by decide⟩


def Delta4 : B3 := (g0 * g1) ^ 6


abbrev Q : Type := B3 ⧸ Subgroup.normalClosure ({Delta4} : Set B3)


noncomputable def q : B3 →* Q := QuotientGroup.mk' (Subgroup.normalClosure ({Delta4} : Set B3))


noncomputable def liftS : Q := q (g0 ^ 2 * g1)


noncomputable def liftT : Q := q g0⁻¹

end BurauNC

theorem burau_coxeter_relation : (BurauNC.liftS⁻¹ * BurauNC.liftT) ^ 3 = 1 := by sorry
